"""Slow reference implementations of the EFX check, straight from the task
statement.  Used only to cross-validate verifier.c; numpy version enumerates
all n^m allocations, the pure-python one checks a single allocation."""

import numpy as np

MP_BIG = np.int64(1) << 50          # stand-in for "no positive good in bundle"
WORST_NONE = -(np.int64(1) << 40)   # stand-in for "no defined pair"
SLACK_UTOPIA = 1 << 40
SUM_SAT = 1 << 60


def is_surviving(V, alloc, tau=1, relation="efx"):
    """Single-allocation check, literal transcription of the definition."""
    n, m = len(V), len(V[0])
    bundles = [[g for g in range(m) if alloc[g] == a] for a in range(n)]
    for i in range(n):
        own = sum(V[i][g] for g in bundles[i])
        for j in range(n):
            if i == j:
                continue
            vj = sum(V[i][g] for g in bundles[j])
            if relation == "ef":
                if vj - own >= tau:
                    return False
            else:
                for g in bundles[j]:
                    if V[i][g] > 0 and (vj - V[i][g]) - own >= tau:
                        return False
    return True


def check_all(V, tau=1, relation="efx"):
    """Enumerate all n^m allocations with numpy; returns the same
    (count, min_slack, sum_slack) statistics as verifier.c."""
    V = np.asarray(V, dtype=np.int64)
    n, m = V.shape
    N = n ** m
    idx = np.arange(N, dtype=np.int64)
    powers = n ** np.arange(m, dtype=np.int64)
    D = ((idx[:, None] // powers[None, :]) % n).astype(np.int8)  # (N, m)

    masks = [(D == j) for j in range(n)]                     # each (N, m) bool
    S = np.empty((n, n, N), dtype=np.int64)                  # S[i][j] = v_i(A_j)
    for j in range(n):
        S[:, j, :] = (masks[j].astype(np.int64) @ V.T).T

    worst = np.full(N, WORST_NONE, dtype=np.int64)
    for i in range(n):
        pos = V[i] > 0
        for j in range(n):
            if i == j:
                continue
            if relation == "ef":
                d = S[i, j] - S[i, i]
                np.maximum(worst, d, out=worst)
            else:
                vals = np.where(masks[j] & pos[None, :], V[i][None, :], MP_BIG)
                mp = vals.min(axis=1)
                defined = mp < MP_BIG
                d = (S[i, j] - mp) - S[i, i]
                upd = defined & (d > worst)
                worst[upd] = d[upd]

    survive = worst < tau
    count = int(survive.sum())
    if count == 0:
        return {"count": 0, "min_slack": np.iinfo(np.int64).max, "sum_slack": 0}
    sl = np.where(worst == WORST_NONE, SLACK_UTOPIA, -worst)[survive]
    return {
        "count": count,
        "min_slack": int(sl.min()),
        "sum_slack": int(min(int(sl.sum()), SUM_SAT)),
    }
