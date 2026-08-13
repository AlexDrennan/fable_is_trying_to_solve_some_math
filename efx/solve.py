#!/usr/bin/env python3
"""Drive the CP-SAT search for an additive-EFX counterexample.

Modes:
  controls        sanity suite: fixed-V consistency (encoder <-> C verifier),
                  EF SAT control, known-theorem UNSAT controls
  eager           full encoding of all n^m allocation clauses, then solve
  cegar           incremental clause generation against the C verifier

Every run appends a JSON record to efx/runs/.  A FEASIBLE result is only
reported as a counterexample after independent re-verification with the C
verifier (and it would still be re-checked with reference.py before anyone
believes it).
"""

import argparse
import json
import os
import random
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import native
from encode import EFXEncoder

RUNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
CAND = os.path.join(os.path.dirname(os.path.abspath(__file__)), "candidates")


def git_sha():
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"],
                                       text=True).strip()
    except Exception:
        return "unknown"


def record(tag, payload):
    os.makedirs(RUNS, exist_ok=True)
    payload = {"tag": tag, "git_sha": git_sha(), "argv": sys.argv[1:],
               "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               **payload}
    path = os.path.join(RUNS, f"{tag}.json")
    with open(path, "w") as fh:
        json.dump(payload, fh, indent=1)
    print(f"[{tag}] {payload.get('status', '?')} "
          f"wall={payload.get('wall', 0):.1f}s -> {path}")
    return payload


def build(n, m, B, lo, relation, restrictions, lex, eager,
          pos_skeleton=False, mono=False):
    enc = EFXEncoder(n, m, B, lo=lo, relation=relation,
                     pos_skeleton=pos_skeleton)
    if lex:
        enc.add_double_lex()
    if "rowcol" in restrictions:
        enc.add_row_col_nonzero()
    if "support4" in restrictions:
        enc.add_support_at_least(4)
    if eager:
        enc.add_all_allocs()
        if mono:
            enc.add_monotone_implications()
    return enc


def verify_candidate(V, relation):
    """Full recount with the C verifier; count == 0 means counterexample."""
    return native.verify(V, tau=1, cap=0, relation=1 if relation == "ef" else 0)


def handle_feasible(tag, V, relation):
    chk = verify_candidate(V, relation)
    ok = chk["count"] == 0
    os.makedirs(CAND, exist_ok=True)
    path = os.path.join(CAND, f"{tag}_{'CONFIRMED' if ok else 'INVALID'}.json")
    with open(path, "w") as fh:
        json.dump({"V": V, "verifier": {k: chk[k] for k in
                                        ("count", "min_slack", "aborted")}},
                  fh, indent=1)
    if ok and relation == "efx":
        print("!!! CANDIDATE COUNTEREXAMPLE CONFIRMED BY C VERIFIER:", path)
    elif not ok:
        print(f"!!! ENCODING BUG: solver FEASIBLE but verifier count="
              f"{chk['count']} — see {path}")
    return ok, chk


def run_controls(args):
    rng = random.Random(7)
    bad = 0

    # (a) fixed-V consistency: encoder and verifier must agree on whether a
    # concrete matrix is a counterexample (no lex / no restrictions here!)
    cfgs = [(4, 6, 2, 0.0)] * 3 + [(4, 6, 9, 0.4)] * 3 + \
           [(4, 6, 2, 0.4)] * 3 + [(4, 6, 9, 0.0)] * 3 + [(4, 7, 3, 0.3)] * 2
    t0 = time.time()
    for k, (n, m, B, p) in enumerate(cfgs):
        V = [[0 if rng.random() < p else rng.randint(0, B) for _ in range(m)]
             for _ in range(n)]
        enc = build(n, m, B, 0, "efx", [], lex=False, eager=True)
        enc.fix_values(V)
        res = enc.solve(time_limit=60, workers=4)
        want_sat = native.verify(V, tau=1, cap=1)["count"] == 0
        got_sat = res["status"] in ("FEASIBLE", "OPTIMAL")
        if res["status"] == "UNKNOWN" or want_sat != got_sat:
            bad += 1
            print(f"fixed-V MISMATCH #{k}: solver={res['status']} "
                  f"verifier_count0={want_sat} V={V}")
    print(f"[a] fixed-V consistency: {len(cfgs)} cases, {bad} mismatches, "
          f"{time.time()-t0:.0f}s")

    # (a') fixed-V SAT side via EF: universally-loved single good has no
    # envy-free allocation, so the EF encoder must say FEASIBLE
    V = [[1] + [0] * 5 for _ in range(4)]
    enc = build(4, 6, 3, 0, "ef", [], lex=False, eager=True)
    enc.fix_values(V)
    res = enc.solve(time_limit=60, workers=4)
    if res["status"] not in ("FEASIBLE", "OPTIMAL"):
        bad += 1
        print(f"fixed-V EF control FAILED: {res['status']}")
    print("[a'] fixed-V EF SAT side ok" if not bad else "[a'] see above")

    # (b) free-V EF SAT control: some matrix with NO envy-free allocation
    # exists at (4,6); pipeline must find and confirm one end to end
    enc = build(4, 6, 3, 0, "ef", [], lex=True, eager=True)
    res = enc.solve(time_limit=120, workers=4)
    okb = False
    if res["status"] in ("FEASIBLE", "OPTIMAL"):
        okb, chk = handle_feasible("control_ef_4x6", res["V"], "ef")
    if not okb:
        bad += 1
        print(f"[b] EF SAT control FAILED: {res['status']}")
    else:
        print("[b] EF SAT control ok (found + confirmed EF-counterexample)")

    # (c) theorem UNSAT controls: EFX exists for n=2 (Plaut-Roughgarden) and
    # for m <= n+3 (Mahara), so these must be UNSAT (UNKNOWN = inconclusive)
    for tag, (n, m, B, cap) in {
        "control_unsat_2x5": (2, 5, 3, 120),
        "control_unsat_3x6": (3, 6, 2, 180),
    }.items():
        enc = build(n, m, B, 0, "efx", ["rowcol"], lex=True, eager=True)
        res = enc.solve(time_limit=cap, workers=4)
        record(tag, {"n": n, "m": m, "B": B, **res})
        if res["status"] == "INFEASIBLE":
            print(f"[c] {tag}: UNSAT as the theorem requires")
        elif res["status"] in ("FEASIBLE", "OPTIMAL"):
            ok, _ = handle_feasible(tag, res["V"], "efx")
            bad += 1
            print(f"[c] {tag}: FEASIBLE — {'THEOREM-CONTRADICTING (bug!)' if ok else 'encoding bug'}")
        else:
            print(f"[c] {tag}: {res['status']} (inconclusive, not a failure)")

    print(f"CONTROLS DONE, {bad} hard failures")
    return 1 if bad else 0


def run_eager(args):
    t0 = time.time()
    enc = build(args.n, args.m, args.B, args.lo, args.relation,
                args.restrictions.split(",") if args.restrictions else [],
                lex=not args.no_lex, eager=True,
                pos_skeleton=args.pos_skeleton, mono=args.mono)
    build_s = time.time() - t0
    print(f"model built in {build_s:.0f}s: {enc.clauses} allocation clauses, "
          f"{len(enc._viol)} viol lits, {len(enc._bsum)} bsums")
    res = enc.solve(time_limit=args.time, workers=args.workers,
                    seed=args.seed)
    out = {"n": args.n, "m": args.m, "B": args.B, "lo": args.lo,
           "relation": args.relation, "restrictions": args.restrictions,
           "lex": not args.no_lex, "build_s": build_s,
           "clauses": enc.clauses, **res}
    if res["status"] in ("FEASIBLE", "OPTIMAL"):
        ok, chk = handle_feasible(args.tag, res["V"], args.relation)
        out["confirmed"] = ok
        out["verifier_count"] = chk["count"]
    record(args.tag, out)
    return 0


def run_cegar(args):
    rng = random.Random(args.seed)
    n, m = args.n, args.m
    enc = build(n, m, args.B, args.lo, args.relation,
                args.restrictions.split(",") if args.restrictions else [],
                lex=not args.no_lex, eager=False)
    seen = set()

    def add(alloc):
        t = tuple(alloc)
        if t not in seen:
            seen.add(t)
            enc.add_alloc_clause(t)

    for a in range(n):                       # "everything to one agent"
        add([a] * m)
    for _ in range(args.seed_clauses):
        add([rng.randrange(n) for _ in range(m)])

    t_end = time.time() + args.time
    hint = None
    it = 0
    status = "UNKNOWN"
    while time.time() < t_end:
        it += 1
        res = enc.solve(time_limit=min(args.iter_time, t_end - time.time()),
                        workers=args.workers, seed=args.seed, hint=hint)
        status = res["status"]
        if status == "INFEASIBLE":
            print(f"iter {it}: UNSAT with {len(seen)} clauses — certificate "
                  f"(subset of clauses already unsatisfiable)")
            break
        if status not in ("FEASIBLE", "OPTIMAL"):
            print(f"iter {it}: {status}, stopping")
            break
        V = res["V"]
        hint = V
        chk = native.verify(V, tau=1, cap=args.batch,
                            relation=1 if args.relation == "ef" else 0,
                            collect=args.batch)
        if chk["count"] == 0:
            ok, _ = handle_feasible(args.tag, V, args.relation)
            status = "COUNTEREXAMPLE" if ok else "ENCODING-BUG"
            break
        for alloc in chk["allocs"]:
            add(alloc)
        print(f"iter {it}: candidate survives >= {chk['count']} allocations, "
              f"clauses now {len(seen)}")
    record(args.tag, {"n": n, "m": m, "B": args.B, "iters": it,
                      "clauses": len(seen), "status": status,
                      "wall": args.time})
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["controls", "eager", "cegar"])
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--m", type=int, default=8)
    ap.add_argument("--B", type=int, default=3)
    ap.add_argument("--lo", type=int, default=0)
    ap.add_argument("--relation", default="efx", choices=["efx", "ef"])
    ap.add_argument("--restrictions", default="rowcol")
    ap.add_argument("--no-lex", action="store_true")
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--iter-time", type=float, default=60)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--seed-clauses", type=int, default=2000)
    ap.add_argument("--batch", type=int, default=1000)
    ap.add_argument("--pos-skeleton", action="store_true")
    ap.add_argument("--mono", action="store_true")
    ap.add_argument("--tag", default="run")
    args = ap.parse_args()
    if args.mode == "controls":
        return run_controls(args)
    if args.mode == "eager":
        return run_eager(args)
    return run_cegar(args)


if __name__ == "__main__":
    sys.exit(main())
