#!/usr/bin/env python3
"""Cross-validate verifier.c against the reference implementations.

Checks, in order:
  1. fixed known-answer instance;
  2. random matrices: C (count, min_slack, sum_slack) == numpy reference,
     across sizes, value bounds, zero densities, tau, and both relations;
  3. collect mode: every allocation returned by C survives per the literal
     definition (original good order — catches permutation bugs);
  4. Mahara property spot check: m = n + 3 additive instances always admit
     an EFX allocation (count >= 1) — a count of 0 here means a bug.
Exit code 0 iff everything agrees.
"""

import random
import sys

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))

import native
import reference


def rand_matrix(rng, n, m, B, zero_p):
    return [[0 if rng.random() < zero_p else rng.randint(0, B) for _ in range(m)]
            for _ in range(n)]


def main():
    rng = random.Random(20260813)
    failures = 0

    # 1. fixed instance: single universally-loved good
    V = [[1, 0, 0, 0, 0, 0] for _ in range(4)]
    r_efx = native.verify(V, tau=1, relation=0)
    r_ef = native.verify(V, tau=1, relation=1)
    assert r_efx["count"] == 4 ** 6, r_efx   # removing the good erases all envy
    assert r_ef["count"] == 0, r_ef          # someone always envies the holder
    print("[1] fixed instance ok")

    # 2. random cross-validation
    sizes = [(2, 6), (3, 5), (3, 6), (4, 5), (4, 6), (4, 7), (4, 8),
             (5, 5), (5, 6), (6, 5)]
    cases = 0
    for trial in range(240):
        n, m = sizes[trial % len(sizes)]
        B = rng.choice([1, 3, 9, 100])
        zero_p = rng.choice([0.0, 0.3, 0.6])
        tau = rng.choice([1, 1, 1, 2, 5])
        relation = rng.choice([0, 0, 0, 1])
        V = rand_matrix(rng, n, m, B, zero_p)
        got = native.verify(V, tau=tau, relation=relation)
        want = reference.check_all(V, tau=tau,
                                   relation="ef" if relation else "efx")
        keyg = (got["count"], got["min_slack"], got["sum_slack"])
        keyw = (want["count"], want["min_slack"], want["sum_slack"])
        if keyg != keyw:
            failures += 1
            print(f"MISMATCH n={n} m={m} B={B} p={zero_p} tau={tau} "
                  f"rel={relation}: C={keyg} ref={keyw}\n  V={V}")
        cases += 1
    print(f"[2] random cross-validation: {cases} cases, {failures} mismatches")

    # 3. collect-mode validation
    for _ in range(20):
        V = rand_matrix(rng, 4, 7, 9, 0.3)
        got = native.verify(V, tau=1, relation=0, cap=0, collect=50)
        for alloc in got.get("allocs", []):
            if not reference.is_surviving(V, alloc, tau=1):
                failures += 1
                print(f"BAD COLLECTED ALLOC {alloc} for V={V}")
    print("[3] collect-mode validation done")

    # 4. Mahara spot check (m = n + 3 => EFX exists)
    zero_counts = 0
    for _ in range(100):
        V = rand_matrix(rng, 4, 7, 9, rng.choice([0.0, 0.3]))
        got = native.verify(V, tau=1, relation=0, cap=1)
        if got["count"] == 0:
            zero_counts += 1
            print(f"UNEXPECTED count=0 at (4,7): V={V}")
    if zero_counts:
        failures += zero_counts
    print(f"[4] Mahara spot check: {zero_counts} zero-count instances (expect 0)")

    if failures:
        print(f"FAILED: {failures} problems")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
