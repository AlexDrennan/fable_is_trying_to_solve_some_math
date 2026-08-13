#!/usr/bin/env python3
"""Simulated annealing over valuation matrices, minimizing the number of EFX
allocations.  Energy E(V) = count + sum_slack/(sum_slack+1): the fractional
term breaks ties among equal counts toward tighter surviving allocations
(without ever reordering different counts).  count = 0 would be a
counterexample to EFX existence — verified independently before celebrating.

Evaluation uses the C verifier through ctypes with cap = current_count + 1:
an aborted run proves the proposal is strictly worse than the incumbent, so
it can be rejected cheaply without a full count.
"""

import argparse
import json
import math
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import native

CAND = os.path.join(os.path.dirname(os.path.abspath(__file__)), "candidates")
RUNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")

# typed mode: state is the n x t type-value matrix W; evaluation expands it
# to the flat matrix (identical columns per type) — see typed.py
TYPES = None


def to_flat(V):
    if TYPES is None:
        return V
    cols = [k for k, ck in enumerate(TYPES) for _ in range(ck)]
    return [[row[k] for k in cols] for row in V]


def energy(V, cap):
    r = native.verify(to_flat(V), tau=1, cap=cap)
    if r["aborted"]:
        return r["count"] + 1.0, r          # lower bound; enough to reject
    frac = r["sum_slack"] / (r["sum_slack"] + 1.0)
    return r["count"] + frac, r


def clampf(x, lo, B):
    return max(lo, min(B, x))


def init_nearmiss(rng, n, m, B, lo):
    """V*-inspired: one near-flat agent, one universally-big column,
    a few epsilon goods, rest random."""
    V = [[rng.randint(max(lo, B // 4), B) for _ in range(m)]
         for _ in range(n)]
    flat = rng.randrange(n)
    base = rng.randint(B // 3, 2 * B // 3)
    V[flat] = [base + rng.randint(-2, 2) for _ in range(m)]
    gbig = rng.randrange(m)
    for i in range(n):
        V[i][gbig] = rng.randint(9 * B // 10, B)
    for _ in range(rng.randint(2, 3)):      # epsilon goods
        g = rng.randrange(m)
        for i in range(n):
            V[i][g] = clampf(rng.randint(1, max(2, B // 100)), lo, B)
    return [[clampf(v, lo, B) for v in row] for row in V]


def init_matrix(rng, n, m, B, kind):
    if kind == "identical":
        base = [rng.randint(0, B) for _ in range(m)]
        return [[max(0, min(B, v + rng.randint(-B // 10 - 1, B // 10 + 1)))
                 for v in base] for _ in range(n)]
    if kind == "bivalued":
        a, b = sorted(rng.sample(range(1, B + 1), 2))
        return [[rng.choice([a, b]) + rng.randint(-2, 2) for _ in range(m)]
                for _ in range(n)]
    if kind == "favorites":
        V = [[rng.randint(0, B // 10 + 1) for _ in range(m)] for _ in range(n)]
        goods = list(range(m))
        rng.shuffle(goods)
        for i in range(n):
            for k in range(m // n):
                V[i][goods[(i * (m // n) + k) % m]] = rng.randint(B // 2, B)
        return V
    return [[0 if rng.random() < 0.15 else rng.randint(0, B)
             for _ in range(m)] for _ in range(n)]


def mutate(rng, V, B):
    n, m = len(V), len(V[0])
    W = [row[:] for row in V]
    r = rng.random()
    if r < 0.50:                       # nudge one entry
        i, g = rng.randrange(n), rng.randrange(m)
        delta = rng.choice([-1, 1]) * max(1, int(abs(rng.gauss(0, B * 0.05))))
        W[i][g] = max(0, min(B, W[i][g] + delta))
    elif r < 0.70:                     # resample one entry
        i, g = rng.randrange(n), rng.randrange(m)
        W[i][g] = 0 if rng.random() < 0.15 else rng.randint(0, B)
    elif r < 0.85:                     # swap two entries within a row
        i = rng.randrange(n)
        g1, g2 = rng.randrange(m), rng.randrange(m)
        W[i][g1], W[i][g2] = W[i][g2], W[i][g1]
    else:                              # clone another column + noise
        g1, g2 = rng.randrange(m), rng.randrange(m)
        for i in range(n):
            W[i][g2] = max(0, min(B, W[i][g1] + rng.randint(-3, 3)))
    return W


def save_near_miss(tag, V, r, evals):
    os.makedirs(CAND, exist_ok=True)
    path = os.path.join(CAND, f"nearmiss_{tag}_c{r['count']}.json")
    with open(path, "w") as fh:
        json.dump({"V": V, "count": r["count"], "min_slack": r["min_slack"],
                   "evals": evals}, fh)
    return path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--m", type=int, default=None,
                    help="goods count (flat mode); ignored with --types")
    ap.add_argument("--B", type=int, default=1000)
    ap.add_argument("--lo", type=int, default=0,
                    help="lower bound for values (Archimedean-middle runs)")
    ap.add_argument("--types", default=None,
                    help="comma multiplicities: typed SA over W (n x t)")
    ap.add_argument("--init-file", default=None,
                    help="runs/*.json with best_V/V to seed the first restart")
    ap.add_argument("--seconds", type=float, default=420)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--tag", default=None)
    args = ap.parse_args()
    global TYPES
    if args.types:
        TYPES = tuple(int(x) for x in args.types.split(","))
    tag = args.tag or (f"sa_{args.n}x{args.m}_s{args.seed}" if not TYPES else
                       f"sa_typed_{args.n}x{'-'.join(map(str, TYPES))}_s{args.seed}")
    rng = random.Random(args.seed)
    n, B = args.n, args.B
    if TYPES is None and args.m is None:
        ap.error("--m is required without --types")
    m = len(TYPES) if TYPES else args.m   # state width (t in typed mode)
    seed_V = None
    if args.init_file:
        with open(args.init_file) as fh:
            rec = json.load(fh)
        seed_V = rec.get("best_V") or rec.get("V") or rec.get("W")

    best_E, best_V, best_r = math.inf, None, None
    t_end = time.time() + args.seconds
    evals = 0
    restarts = -1
    while time.time() < t_end:
        restarts += 1
        if seed_V is not None and restarts == 0:
            V = [row[:] for row in seed_V]
        elif restarts % 5 == 4:
            V = init_nearmiss(rng, n, m, B, args.lo)
        else:
            V = init_matrix(rng, n, m, B, ["random", "identical",
                                           "favorites", "bivalued"
                                           ][restarts % 4])
        if args.lo:
            V = [[clampf(v, args.lo, B) for v in row] for row in V]
        E, r = energy(V, cap=0)
        evals += 1
        T0 = max(4.0, E * 0.05)
        T = T0
        stall = 0
        while time.time() < t_end and stall < 3000:
            W = mutate(rng, V, B)
            if args.lo:
                W = [[clampf(v, args.lo, B) for v in row] for row in W]
            cap = int(E) + 1
            EW, rW = energy(W, cap)
            evals += 1
            improved = EW < E
            if improved or rng.random() < math.exp(-(EW - E) / max(T, 1e-9)):
                if not rW["aborted"]:
                    V, E, r = W, EW, rW
                    if improved:
                        stall = 0
            stall += 1
            T = max(0.02, T * 0.9995)
            if E < best_E:
                best_E, best_V, best_r = E, [row[:] for row in V], r
                if r["count"] <= 10:
                    save_near_miss(tag, best_V, r, evals)
                if r["count"] == 0:
                    chk = native.verify(best_V, tau=1, cap=0)
                    print(f"!!! count=0 at evals={evals}: recheck={chk}")
                    if chk["count"] == 0:
                        os.makedirs(CAND, exist_ok=True)
                        with open(os.path.join(
                                CAND, f"COUNTEREXAMPLE_{tag}.json"), "w") as fh:
                            json.dump(best_V, fh)
                        break
        if best_r is not None and best_r["count"] == 0:
            break

    os.makedirs(RUNS, exist_ok=True)
    out = {"tag": tag, "n": n, "m": m, "B": B, "seed": args.seed,
           "evals": evals, "restarts": restarts + 1,
           "best_count": best_r["count"] if best_r else None,
           "best_min_slack": best_r["min_slack"] if best_r else None,
           "best_V": best_V}
    with open(os.path.join(RUNS, f"{tag}.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"[{tag}] evals={evals} best_count={out['best_count']} "
          f"best_min_slack={out['best_min_slack']}")


if __name__ == "__main__":
    main()
