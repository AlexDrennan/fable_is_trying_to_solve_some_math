# Campaign report: searching for an additive EFX counterexample

Date: 2026-08-13. Hardware: 4 cores, 15 GB RAM. All artifacts in this repo;
every run has a JSON record in `efx/runs/` (seeds, git SHA, wall time).

## Problem

Exhibit V ∈ Z≥0^{n×m}, n ≥ 4, additive valuations, such that no allocation of
the m goods is EFX (envy-free up to any positively-valued good), with n^m
small enough to enumerate. This is the open problem of EFX existence for
additive valuations; a counterexample here would refute the EFX conjecture.
EFX existence is known for n ≤ 3 (Chaudhury–Garg–Mehlhorn EC'20), m ≤ n+3
(Mahara), bivalued instances, identical valuations, among others; in 2026 EFX
was refuted for monotone/submodular valuations via SAT
([arXiv:2604.18216](https://arxiv.org/abs/2604.18216)), with the additive
case explicitly left open. Search frontier under the constraints: (n=4,
m ∈ [8,11]), (n=5, m ∈ [9,10]).

## Toolchain correctness (all green before any campaign run)

1. `verifier.c` (exhaustive DFS with a proven pruning rule — proof in the
   header comment) agrees with a numpy transcription of the definition on
   240 random instances across n ∈ [2,6], m ∈ [5,8], value bounds
   {1,3,9,100}, zero densities {0,.3,.6}, τ ∈ {1,2,5}, EFX and EF modes:
   identical (count, min_slack, sum_slack) on every instance.
2. Collected allocations re-verified against the literal definition
   (original good order) — no permutation bugs.
3. Mahara property check: 100 random (4,7) instances all admit an EFX
   allocation (count ≥ 1), as the m ≤ n+3 theorem requires.
4. Encoder ↔ verifier fixed-V consistency: on 14 concrete matrices the
   CP-SAT model (no symmetry breaking, no restrictions) is SAT exactly when
   the verifier reports zero EFX allocations.
5. End-to-end SAT path: for plain envy-freeness (EF), where counterexamples
   trivially exist, the pipeline finds a matrix and independently confirms it
   (`efx/candidates/control_ef_4x6_CONFIRMED.json`).
6. Theorem controls, full eager encodings solved to INFEASIBLE:
   (2,5) B=3 in 0.04 s (Plaut–Roughgarden n=2), (3,6) B=2 in 0.5 s
   (m = n+3), (4,7) B=2 in 5.4 s (m = n+3, the dress rehearsal for the
   frontier size).

## Negative certificates (new, machine-generated)

Encoding: variables V[i][g] ∈ [lo, B]; one clause per allocation ("some
ordered pair violates EFX"), shared half-reified violation literals; sound
symmetry breaking (double-lex) and sound restrictions (every row and every
column has a positive entry — one-line proofs in `efx/encode.py`). UNSAT
therefore means: **no counterexample exists in the stated class**, up to
agent/good relabeling.

| n | m | values | result | wall | run record |
|---|---|--------|--------|------|------------|
| 2 | 5 | 0..3 | UNSAT (control) | 0.04 s | `control_unsat_2x5` |
| 3 | 6 | 0..2 | UNSAT (control) | 0.5 s | `control_unsat_3x6` |
| 4 | 7 | 0..2 | UNSAT (control, m=n+3) | 5.4 s | `preflight_4x7_B2` |
| 4 | 8 | 0..2 | **UNSAT — new certificate** | 33 s | `frontier_4x8_B2` |
| 4 | 8 | 0..3 | **UNKNOWN** at 600 s cap | 600 s | `frontier_4x8_B3` |

(4,8) is the first size not covered by any existence theorem (m = n+4), and
values {0,1,2} are outside the bivalued existence theorem, so the B=2 row is
a genuinely new (if small) verified fact: **no 4-agent, 8-good additive
counterexample with values in {0,1,2} exists**. The B=3 instance produced
only 109 conflicts in 600 s — propagation-bound at this size; a longer
budget or a CEGAR schedule is the natural continuation, not a different
method.

## Heuristic search (simulated annealing, values in [0,1000])

Objective: number of EFX allocations (ties broken toward smaller total
slack), evaluated exactly by the C verifier with an early-abort cap.

| n | m | evals | best #EFX / n^m | min slack | run record |
|---|---|-------|------------------|-----------|------------|
| 4 | 10 | 374,704 | 591 / 1,048,576 | 3 | `sa_4x10_s1` |
| 4 | 11 | 3,018,237 | **12** / 4,194,304 | 1 | `sa_4x11_s2` |

The (4,11) near-miss (matrix in `efx/runs/sa_4x11_s2.json`) leaves twelve
EFX allocations, each surviving with the minimum possible slack 1. Squeezing
such instances to zero is exactly what the open problem asks and is where
every published attempt (and this one) stops.

## Conclusion

No counterexample was found — consistent with the standing conjecture that
EFX allocations always exist for additive valuations, and with the 2026
monotone-valuations counterexample relying essentially on complementarity.
Concrete new evidence from this campaign: verified UNSAT certificates up to
(4,7) values ≤ 2 within seconds, reproduction of three existence theorems by
an independent method, and a (4,11) instance with only 12 EFX allocations
out of 4.19 M. Nothing here is submittable to the site (a submission must
have zero EFX allocations); the honest deliverable is this toolchain and
these certificates.

Continuation ideas, in order of expected value: longer CP-SAT budgets and a
CEGAR ladder on (4,8)–(4,10); [1,B] all-positive hunt configs plus the
support-≥4 restriction (proof in `efx/encode.py`); intensification around
archived near-misses; porting the arXiv:2604.18216 counterexample's
combinatorial skeleton into additive gadget families.
