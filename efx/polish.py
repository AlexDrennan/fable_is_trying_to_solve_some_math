#!/usr/bin/env python3
"""Ball-CEGAR polishing of a near-miss matrix.

The (4,11) near-miss V* has 12 EFX allocations, every one surviving with
slack exactly 1 — V* sits on a wall of the integer lattice, so searching at
scale 1 cannot cross it.  We refine the lattice instead: look for an integer
matrix W with |W - s*V*|_inf <= r (scale s = 10, then 100), radius ladder,
such that no allocation is EFX.  CEGAR loop: CP-SAT proposes W killing all
survivors collected so far; the C verifier reports W's actual survivors;
their kill clauses are added; repeat.

Outcomes: either a genuine counterexample (triple-checked), or a LOCAL
RIGIDITY CERTIFICATE — "no integer matrix within L_inf radius r of s*V*
kills every allocation" — plus a survivor-birth log showing which
allocations keep resurrecting (hypothesis: the rotation family of the
epsilon-good g0).

No symmetry breaking and no domain restrictions here: the frame must stay
fixed for the kill clauses to keep their meaning.
"""

import argparse
import json
import os
import subprocess
import sys
import time

from ortools.sat.python import cp_model

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import native
import reference

RUNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
CAND = os.path.join(os.path.dirname(os.path.abspath(__file__)), "candidates")


class BallModel:
    def __init__(self, Vstar, scale, r, free=False, B=None):
        self.n, self.m = len(Vstar), len(Vstar[0])
        self.center = [[scale * v for v in row] for row in Vstar]
        self.model = cp_model.CpModel()
        hi_all = 0
        self.W = []
        for i in range(self.n):
            row = []
            for g in range(self.m):
                c = self.center[i][g]
                lo, hi = (0, B) if free else (max(0, c - r), c + r)
                row.append(self.model.NewIntVar(lo, hi, f"W_{i}_{g}"))
                hi_all = max(hi_all, hi)
            self.W.append(row)
        self.maxv = hi_all
        self._mp = {}
        self._bsum = {}
        self.kill_count = 0

    def bsum(self, i, S):
        if not S:
            return 0
        key = (i, S)
        v = self._bsum.get(key)
        if v is None:
            v = self.model.NewIntVar(0, self.maxv * len(S), f"bs_{i}_{key}")
            self.model.Add(v == sum(self.W[i][g] for g in S))
            self._bsum[key] = v
        return v

    def mp_hp(self, i, T):
        key = (i, T)
        r = self._mp.get(key)
        if r is None:
            mp = self.model.NewIntVar(1, self.maxv, f"mp_{i}_{key}")
            hp = self.model.NewBoolVar(f"hp_{i}_{key}")
            sels = []
            for g in T:
                sl = self.model.NewBoolVar("")
                self.model.Add(self.W[i][g] >= 1).OnlyEnforceIf(sl)
                self.model.Add(self.W[i][g] <= mp).OnlyEnforceIf(sl)
                sels.append(sl)
            self.model.AddBoolOr(sels).OnlyEnforceIf(hp)
            r = (mp, hp)
            self._mp[key] = r
        return r

    def add_kill(self, alloc):
        """Clause: allocation `alloc` (tuple, agent per good) is not EFX."""
        bundles = [tuple(g for g in range(self.m) if alloc[g] == a)
                   for a in range(self.n)]
        lits = []
        for i in range(self.n):
            for j in range(self.n):
                if i == j or not bundles[j]:
                    continue
                v = self.model.NewBoolVar("")
                mp, hp = self.mp_hp(i, bundles[j])
                self.model.AddImplication(v, hp)
                self.model.Add(self.bsum(i, bundles[i])
                               - self.bsum(i, bundles[j]) + mp
                               <= -1).OnlyEnforceIf(v)
                lits.append(v)
        self.model.AddBoolOr(lits)
        self.kill_count += 1

    def solve(self, time_limit, hint=None, workers=2):
        if hint is not None:
            for i in range(self.n):
                for g in range(self.m):
                    self.model.AddHint(self.W[i][g], int(hint[i][g]))
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = float(time_limit)
        s.parameters.num_workers = int(workers)
        st = s.Solve(self.model)
        name = s.StatusName(st)
        out = {"status": name, "wall": s.WallTime()}
        if name in ("FEASIBLE", "OPTIMAL"):
            out["W"] = [[int(s.Value(self.W[i][g])) for g in range(self.m)]
                        for i in range(self.n)]
        return out


def triple_check(tag, W):
    chk = native.verify(W, tau=1, cap=0)
    ok = chk["count"] == 0
    if ok:
        import random
        rng = random.Random(0)
        n, m = len(W), len(W[0])
        for _ in range(3000):
            if reference.is_surviving(W, [rng.randrange(n)
                                          for _ in range(m)], tau=1):
                ok = False
                break
    os.makedirs(CAND, exist_ok=True)
    path = os.path.join(CAND, f"{tag}_{'CONFIRMED' if ok else 'INVALID'}.json")
    with open(path, "w") as fh:
        json.dump({"V": W, "verifier_count": chk["count"]}, fh)
    print(("!!! POLISH COUNTEREXAMPLE CONFIRMED: " if ok
           else "!!! polish claimed hit but verification FAILED: ") + path)
    return ok


def cegar(Vstar, scale, r, wall_cap, iter_cap=100, collect_cap=1024,
          free=False, B=None, workers=2, tag="polish"):
    bm = BallModel(Vstar, scale, r, free=free, B=B)
    seen = set()
    birth_log = []
    hint = bm.center
    t_end = time.time() + wall_cap
    it = 0
    status = "UNKNOWN"
    while time.time() < t_end and it < iter_cap:
        it += 1
        res = bm.solve(min(60, t_end - time.time()), hint=hint,
                       workers=workers)
        status = res["status"]
        if status == "INFEASIBLE":
            status = "RIGID"      # local rigidity certificate at (scale, r)
            break
        if status not in ("FEASIBLE", "OPTIMAL"):
            break
        W = res["W"]
        hint = W
        chk = native.verify(W, tau=1, cap=collect_cap, collect=collect_cap)
        if chk["count"] == 0:
            status = "COUNTEREXAMPLE" if triple_check(tag, W) else "BUG"
            break
        fresh = [a for a in chk["allocs"] if a not in seen]
        for a in fresh:
            seen.add(a)
            bm.add_kill(a)
        birth_log.append({"iter": it, "count": chk["count"],
                          "min_slack": chk["min_slack"],
                          "fresh": len(fresh),
                          "fresh_allocs": [list(a) for a in fresh[:16]]})
        print(f"  iter {it}: survivors>={chk['count']} fresh={len(fresh)} "
              f"kills={bm.kill_count}")
        if not fresh and chk["count"] > 0:
            status = "STALLED"    # survivors known yet still FEASIBLE: bug
            break
    return {"status": status, "iters": it, "kills": bm.kill_count,
            "birth_log": birth_log}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", required=True,
                    help="runs/*.json with best_V (SA record)")
    ap.add_argument("--scales", default="10,100")
    ap.add_argument("--radii", default="1,2,3,5,9")
    ap.add_argument("--radii100", default="10,30,99")
    ap.add_argument("--per-radius", type=float, default=240)
    ap.add_argument("--free", action="store_true",
                    help="heuristic probe: no ball, W in [0,B]")
    ap.add_argument("--B", type=int, default=1000)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--tag", default="polish_4x11")
    args = ap.parse_args()

    with open(args.start) as fh:
        rec = json.load(fh)
    Vstar = rec["best_V"] if "best_V" in rec else rec["V"]
    results = []
    if args.free:
        r = cegar(Vstar, 1, 0, args.per_radius * 3, free=True, B=args.B,
                  workers=args.workers, tag=args.tag + "_free")
        results.append({"mode": "free", **{k: r[k] for k in
                                           ("status", "iters", "kills")}})
        print(f"free probe: {r['status']} after {r['iters']} iters")
    else:
        for scale in (int(s) for s in args.scales.split(",")):
            radii = args.radii if scale == 10 else args.radii100
            for r_ in (int(x) for x in radii.split(",")):
                print(f"scale {scale} radius {r_}:")
                r = cegar(Vstar, scale, r_, args.per_radius,
                          workers=args.workers,
                          tag=f"{args.tag}_s{scale}_r{r_}")
                results.append({"scale": scale, "r": r_, **r})
                if r["status"] in ("COUNTEREXAMPLE", "BUG"):
                    break
            else:
                continue
            break
    try:
        sha = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                      text=True).strip()
    except Exception:
        sha = "unknown"
    os.makedirs(RUNS, exist_ok=True)
    with open(os.path.join(RUNS, f"{args.tag}.json"), "w") as fh:
        json.dump({"tag": args.tag, "git_sha": sha, "start": args.start,
                   "results": results}, fh, indent=1)
    print(f"[{args.tag}] done: " +
          "; ".join(f"s{x.get('scale', 'free')}r{x.get('r', '-')}:"
                    f"{x['status']}" for x in results))


if __name__ == "__main__":
    sys.exit(main())
