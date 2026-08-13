#!/usr/bin/env python3
"""Typed-goods reformulation: t good types with multiplicities c = (c_1..c_t),
agent values W[i][k] per type.  Goods of one type are identical columns, so
EFX status depends only on the count matrix X[a][k] (how many type-k goods
agent a holds): allocations with equal count matrices are related by a
same-type permutation, which preserves every EFX inequality.  Hence

    "no EFX allocation for expand(W, c)"  <=>  "no EFX count matrix",

and the flat number of EFX allocations equals the multinomial-weighted count

    flat_count = sum over surviving X of  prod_k  c_k! / prod_a X[a][k]! .

The count-matrix space has prod_k C(c_k + n - 1, n - 1) elements — e.g.
42,875 for n=4, c=(4,4,4) (m=12) — so exact CP-SAT search reaches m = 12-15
where the flat encoding (n^m clauses) is hopeless.

SCOPE OF CERTIFICATES: a typed UNSAT says "no counterexample whose column
multiset is exactly these t types with these multiplicities, values in
[lo, B], every type positively valued by someone and every agent valuing
something" — it does NOT bound general m-good instances.  (A universally
zero-valued type is inert padding under the positive-good EFX definition,
so those cases are covered by the smaller-shape runs; an all-zero row
reduces to n-1 agents, i.e. CGM for n = 4.)
"""

import argparse
import itertools
import json
import math
import os
import subprocess
import sys
import time

import numpy as np
from ortools.sat.python import cp_model

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import native
import reference

RUNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
CAND = os.path.join(os.path.dirname(os.path.abspath(__file__)), "candidates")
BIG = np.int64(1) << 50


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def enum_count_matrices(c, n):
    """Array (N, n, t): all ways to split c_k goods of each type among n
    agents.  Column a of slice k is agent a's count of type k."""
    per_type = [np.array(list(compositions(ck, n)), dtype=np.int64)
                for ck in c]
    grids = np.meshgrid(*[np.arange(len(p)) for p in per_type],
                        indexing="ij")
    idx = np.stack([g.ravel() for g in grids], axis=1)      # (N, t)
    X = np.stack([per_type[k][idx[:, k]] for k in range(len(c))],
                 axis=2)                                     # (N, n, t)
    return X


def typed_check_all(W, c, tau=1):
    """Full evaluation over count matrices; exact weighted flat count."""
    W = np.asarray(W, dtype=np.int64)
    n, t = W.shape
    X = enum_count_matrices(c, n)
    N = X.shape[0]
    S = np.einsum("Nak,ik->iaN", X, W)                       # v_i(A_a)
    worst = np.full(N, -BIG, dtype=np.int64)
    for i in range(n):
        pos = W[i] > 0
        for j in range(n):
            if i == j:
                continue
            vals = np.where((X[:, j, :] >= 1) & pos[None, :],
                            W[i][None, :], BIG)
            mp = vals.min(axis=1)
            defined = mp < BIG
            d = (S[i, j] - mp) - S[i, i]
            upd = defined & (d > worst)
            worst[upd] = d[upd]
    survive = worst < tau
    surv_idx = np.nonzero(survive)[0]
    cfact = [math.factorial(ck) for ck in c]
    weighted = 0
    for r in surv_idx:
        w = 1
        for k in range(t):
            wk = cfact[k]
            for a in range(n):
                wk //= math.factorial(int(X[r, a, k]))
            w *= wk
        weighted += w
    return {"count_matrices": int(N), "surviving": int(surv_idx.size),
            "weighted": int(weighted), "exists": bool(surv_idx.size),
            "X_surviving": X[surv_idx]}


def expand(W, c):
    """Flat n x m matrix: type k contributes c_k identical columns."""
    cols = []
    for k, ck in enumerate(c):
        cols.extend([k] * ck)
    return [[int(W[i][k]) for k in cols] for i in range(len(W))]


def agreement_gate(trials=40, seed=11):
    """flat_count(expand(W,c)) must equal the multinomial-weighted typed
    count, and existence booleans must match."""
    import random
    rng = random.Random(seed)
    shapes = [(3, (2, 2)), (4, (2, 2)), (4, (3, 2, 2)), (3, (2, 2, 2, 2)),
              (4, (4, 3)), (4, (2, 2, 2)), (4, (3, 3, 2))]
    bad = 0
    for trial in range(trials):
        n, c = shapes[trial % len(shapes)]
        B = rng.choice([2, 5, 9])
        W = [[0 if rng.random() < 0.25 else rng.randint(0, B)
              for _ in range(len(c))] for _ in range(n)]
        got = typed_check_all(W, c)
        want = native.verify(expand(W, c), tau=1, cap=0)
        if got["weighted"] != want["count"] or \
                got["exists"] != (want["count"] > 0):
            bad += 1
            print(f"TYPED MISMATCH n={n} c={c} W={W}: "
                  f"typed={got['weighted']} flat={want['count']}")
    # one big-shape spot check
    n, c = 4, (4, 4, 4)
    W = [[rng.randint(0, 5) for _ in range(3)] for _ in range(4)]
    got = typed_check_all(W, c)
    want = native.verify(expand(W, c), tau=1, cap=0)
    if got["weighted"] != want["count"]:
        bad += 1
        print(f"TYPED MISMATCH (4,4,4): {got['weighted']} vs {want['count']}")
    print(f"typed agreement gate: {trials + 1} cases, {bad} mismatches")
    return bad == 0


class TypedEncoder:
    """CP-SAT: exists W in [lo,B]^{n x t} with no EFX count matrix.
    Same literal structure as encode.py, over count vectors, with the
    pos-skeleton biconditionals from day one."""

    def __init__(self, n, c, B, lo=0):
        self.n, self.c, self.B, self.lo = n, tuple(c), B, lo
        self.t = len(c)
        self.model = cp_model.CpModel()
        self.W = [[self.model.NewIntVar(lo, B, f"W_{i}_{k}")
                   for k in range(self.t)] for i in range(n)]
        self.pos = [[self.model.NewBoolVar(f"pos_{i}_{k}")
                     for k in range(self.t)] for i in range(n)]
        for i in range(n):
            for k in range(self.t):
                self.model.Add(self.W[i][k] >= 1).OnlyEnforceIf(
                    self.pos[i][k])
                self.model.Add(self.W[i][k] <= 0).OnlyEnforceIf(
                    self.pos[i][k].Not())
        self._bsum, self._mp, self._viol = {}, {}, {}
        self.clauses = 0

    def bsum(self, i, S):
        if not any(S):
            return 0
        key = (i, S)
        v = self._bsum.get(key)
        if v is None:
            ub = sum(sk * self.B for sk in S)
            v = self.model.NewIntVar(0, ub, f"bs_{i}_{S}")
            self.model.Add(v == sum(int(S[k]) * self.W[i][k]
                                    for k in range(self.t) if S[k]))
            self._bsum[key] = v
        return v

    def mp_hp(self, i, T):
        key = (i, T)
        r = self._mp.get(key)
        if r is None:
            supp = [k for k in range(self.t) if T[k]]
            mp = self.model.NewIntVar(1, max(self.B, 1), f"mp_{i}_{T}")
            hp = self.model.NewBoolVar(f"hp_{i}_{T}")
            self.model.AddBoolOr([self.pos[i][k] for k in supp]
                                 ).OnlyEnforceIf(hp)
            for k in supp:
                self.model.AddImplication(self.pos[i][k], hp)
            sels = []
            for k in supp:
                sl = self.model.NewBoolVar(f"sel_{i}_{T}_{k}")
                self.model.AddImplication(sl, self.pos[i][k])
                self.model.Add(self.W[i][k] <= mp).OnlyEnforceIf(sl)
                sels.append(sl)
            self.model.AddBoolOr(sels).OnlyEnforceIf(hp)
            r = (mp, hp)
            self._mp[key] = r
        return r

    def viol(self, i, S, T):
        key = (i, S, T)
        v = self._viol.get(key)
        if v is None:
            v = self.model.NewBoolVar(f"viol_{i}_{S}_{T}")
            mp, hp = self.mp_hp(i, T)
            self.model.AddImplication(v, hp)
            self.model.Add(self.bsum(i, S) - self.bsum(i, T) + mp
                           <= -1).OnlyEnforceIf(v)
            self._viol[key] = v
        return v

    def add_all_clauses(self):
        X = enum_count_matrices(self.c, self.n)
        for r in range(X.shape[0]):
            rows = [tuple(int(x) for x in X[r, a, :])
                    for a in range(self.n)]
            keys = set()
            for i in range(self.n):
                for j in range(self.n):
                    if i != j and any(rows[j]):
                        keys.add((i, rows[i], rows[j]))
            self.model.AddBoolOr([self.viol(*k) for k in keys])
            self.clauses += 1

    def add_lex(self):
        def lex_le(xs, ys):
            prev = None
            for k, (x, y) in enumerate(zip(xs, ys)):
                if prev is None:
                    self.model.Add(x <= y)
                else:
                    self.model.Add(x <= y).OnlyEnforceIf(prev)
                if k < len(xs) - 1:
                    e = self.model.NewBoolVar("")
                    if prev is not None:
                        self.model.AddImplication(e, prev)
                    self.model.Add(x == y).OnlyEnforceIf(e)
                    prev = e
        for i in range(self.n - 1):
            lex_le(self.W[i], self.W[i + 1])
        for k in range(self.t - 1):
            if self.c[k] == self.c[k + 1]:  # only equal-multiplicity blocks
                lex_le([self.W[i][k] for i in range(self.n)],
                       [self.W[i][k + 1] for i in range(self.n)])

    def add_rowcol(self):
        for i in range(self.n):
            self.model.AddBoolOr(self.pos[i])
        for k in range(self.t):
            self.model.AddBoolOr([self.pos[i][k] for i in range(self.n)])

    def fix_values(self, W):
        for i in range(self.n):
            for k in range(self.t):
                self.model.Add(self.W[i][k] == int(W[i][k]))

    def solve(self, time_limit, workers=2, seed=0):
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = float(time_limit)
        s.parameters.num_workers = int(workers)
        s.parameters.random_seed = int(seed)
        status = s.Solve(self.model)
        out = {"status": s.StatusName(status), "wall": s.WallTime(),
               "conflicts": s.NumConflicts()}
        if out["status"] in ("FEASIBLE", "OPTIMAL"):
            out["W"] = [[int(s.Value(self.W[i][k])) for k in range(self.t)]
                        for i in range(self.n)]
        return out


def record(tag, payload):
    os.makedirs(RUNS, exist_ok=True)
    try:
        sha = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                      text=True).strip()
    except Exception:
        sha = "unknown"
    payload = {"tag": tag, "git_sha": sha,
               "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               **payload}
    with open(os.path.join(RUNS, f"{tag}.json"), "w") as fh:
        json.dump(payload, fh, indent=1)
    print(f"[{tag}] {payload.get('status')} wall="
          f"{payload.get('wall', 0):.1f}s")
    return payload


def jackpot(tag, W, c):
    """Triple-check a claimed counterexample after expansion."""
    import random
    flat = expand(W, c)
    chk = native.verify(flat, tau=1, cap=0)
    ok = chk["count"] == 0
    if ok:
        rng = random.Random(0)
        n, m = len(flat), len(flat[0])
        for _ in range(2000):     # literal-definition spot checks
            alloc = [rng.randrange(n) for _ in range(m)]
            if reference.is_surviving(flat, alloc, tau=1):
                ok = False
                break
    os.makedirs(CAND, exist_ok=True)
    path = os.path.join(CAND,
                        f"{tag}_{'CONFIRMED' if ok else 'INVALID'}.json")
    with open(path, "w") as fh:
        json.dump({"W": [list(map(int, r)) for r in W], "c": list(c),
                   "flat": flat, "verifier_count": chk["count"]}, fh,
                  indent=1)
    print(("!!! TYPED COUNTEREXAMPLE CONFIRMED: " if ok
           else "!!! typed SAT but verification FAILED (bug): ") + path)
    return ok


def gate_fixed(cases=6, seed=3):
    """Fixed-W consistency: encoder SAT <=> typed/flat count is zero."""
    import random
    rng = random.Random(seed)
    bad = 0
    for _ in range(cases):
        n, c, B = 4, (2, 2, 2), 5
        W = [[rng.randint(0, B) for _ in range(len(c))] for _ in range(n)]
        for i in range(n):
            if not any(W[i]):
                W[i][rng.randrange(len(c))] = 1
        enc = TypedEncoder(n, c, B)
        enc.add_all_clauses()
        enc.fix_values(W)
        res = enc.solve(60, workers=4)
        want_sat = not typed_check_all(W, c)["exists"]
        got_sat = res["status"] in ("FEASIBLE", "OPTIMAL")
        if res["status"] == "UNKNOWN" or want_sat != got_sat:
            bad += 1
            print(f"typed fixed-W MISMATCH: {res['status']} "
                  f"want_sat={want_sat} W={W}")
    print(f"typed fixed-W gate: {cases} cases, {bad} mismatches")
    return bad == 0


def hunt(n, c, B, lo, time_limit, tag, workers=2, seed=0):
    t0 = time.time()
    enc = TypedEncoder(n, c, B, lo=lo)
    enc.add_lex()
    enc.add_rowcol()
    enc.add_all_clauses()
    build_s = time.time() - t0
    res = enc.solve(time_limit, workers=workers, seed=seed)
    out = {"n": n, "c": list(c), "m": sum(c), "B": B, "lo": lo,
           "build_s": build_s, "clauses": enc.clauses,
           "viol_lits": len(enc._viol),
           "scope": ("no counterexample with column multiset exactly "
                     f"{list(c)} types x multiplicities, values in "
                     f"[{lo},{B}], all rows/types positively valued"),
           **res}
    if res["status"] in ("FEASIBLE", "OPTIMAL"):
        out["confirmed"] = jackpot(tag, res["W"], c)
    record(tag, out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["gates", "hunt"])
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--c", default="4,4,4")
    ap.add_argument("--B", type=int, default=3)
    ap.add_argument("--lo", type=int, default=0)
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--tag", default=None)
    args = ap.parse_args()
    if args.mode == "gates":
        ok = agreement_gate() and gate_fixed()
        print("TYPED GATES", "ALL OK" if ok else "FAILED")
        return 0 if ok else 1
    c = tuple(int(x) for x in args.c.split(","))
    tag = args.tag or f"typed_{args.n}x{'-'.join(map(str, c))}_B{args.B}"
    hunt(args.n, c, args.B, args.lo, args.time, tag,
         workers=args.workers, seed=args.seed)
    return 0


if __name__ == "__main__":
    sys.exit(main())
