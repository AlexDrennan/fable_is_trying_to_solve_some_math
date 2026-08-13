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
| 4 | 9 | 0..2 | **UNKNOWN** at 300 s cap | 300 s | `frontier_4x9_B2` |

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
Concrete new evidence from this campaign: a verified UNSAT certificate at
the first theorem-free size — (4,8), values in {0,1,2} — reproduction of
three existence theorems by an independent method, and a (4,11) instance
with only 12 EFX allocations out of 4.19 M. Nothing here is submittable to the site (a submission must
have zero EFX allocations); the honest deliverable is this toolchain and
these certificates.

Continuation ideas, in order of expected value: longer CP-SAT budgets and a
CEGAR ladder on (4,8)–(4,10); [1,B] all-positive hunt configs plus the
support-≥4 restriction (proof in `efx/encode.py`); intensification around
archived near-misses; porting the arXiv:2604.18216 counterexample's
combinatorial skeleton into additive gadget families.

---

# Campaign 2 (same date, ~3h): real-valued tower, typed shapes, rigidity

Motivated by the observation that EFX existence is *provable* in the
non-Archimedean (lexicographic) corner of additive valuations, campaign 2
(a) removes the value-bound caveat from certificates by working over the
reals, (b) reaches m = 12–15 exactly through a typed-goods collapse, and
(c) probes the "Archimedean middle" where any counterexample must live.

**Definitional footnote for every claim below**: EFX with respect to
*positively-valued* goods (the site's definition, `verifier.c` header).
Under the any-good variant (EFX0) the col-nonzero discharge would be
unsound.

## A. Real-valued certificates (QF_LRA, z3 + cvc5 on committed .smt2 files)

Encoding: `efx/smt_encode.py` emits SMT-LIB2 text directly (row sums
normalized to 1 — per-row scaling is a symmetry; positivity skeleton as
biconditionals; monotone implication families entailed by the verifier's
pruning lemma; non-strict double-lex).  Gates before any run: both solvers
UNSAT on (2,4); survivor-drop, EF-SAT and fixed-V mutation tests; a
structural checker that re-derives assertion counts and rebuilds 20 random
clauses literal-by-literal.  UNSAT here means **no counterexample over the
nonnegative REALS at that size** — no bound on values at all.  WLOG
discharges are internal to the tower: col-nonzero at (n,m) via the (n,m−1)
rung, zero rows via the (n−1,m) rung; bases m ≤ n by the size-≤1-bundle
lemma.

| n | m | z3 | cvc5 | meaning |
|---|---|----|------|---------|
| 2 | 4..6 | UNSAT 0.03–2.6 s | UNSAT | Plaut–Roughgarden n=2, reproduced over ℝ |
| 3 | 4..6 | UNSAT 0.1–88 s | UNSAT | CGM/Mahara rungs over ℝ |
| 4 | 6 | **UNSAT 73 s** | **UNSAT 391 s** | m = n+2 for four agents over ℝ, self-contained |
| 4 | 7 | (pending) | (pending) | m = n+3 (Mahara-bound analogue) over ℝ |

Measured engine facts: default z3 tactics stall even on (3,6); the working
configuration is `smt.arith.solver=2` + the positivity skeleton + monotone
families.  CEGAR-ing the universal side does not help UNSAT (the theory
search, not clause volume, is the bottleneck).  The committed
`efx/smt/efx_4x8.smt2` is the overnight target (~10 h+ extrapolated).

## B. Typed-goods certificates (count-matrix collapse, CP-SAT)

Goods of one type are identical columns; EFX status depends only on the
count matrix, so "no EFX allocation" is decided over
Π_k C(c_k+n−1, n−1) count matrices instead of n^m allocations
(`efx/typed.py`; agreement with the flat C verifier proved on 41 random
shapes via the exact multinomial-weighted count identity, fixed-W
consistency 6/6).  Scope: each certificate covers exactly the instances
whose column multiset is the stated shape, all types/rows positively
valued.  All 13 shapes ran UNSAT:

| n | shape (m) | values | wall |
|---|-----------|--------|------|
| 4 | 3+3+3 (9) | 0..3 | 2.1 s |
| 4 | 4+4+4 (12) | 0..3 / 0..5 / **0..9** | 0.2 / 0.1 / 0.4 s |
| 4 | 5+5+5 (**15**) | 0..2 / 0..3 | 82 / 116 s |
| 4 | 6+3+3 (12) | 0..3 | 19 s |
| 4 | 5+4+3 (12) | 0..3 | 28 s |
| 4 | 3+3+3+3 (12) | 0..3 | 115 s |
| 4 | 2+2+2+2+2 (10) | 0..3 | 94 s |
| 5 | 3+3+3 (9) | 0..2 | 3.5 s |
| 5 | 4+4+4 (12) | 0..2 | 26 s |
| 6 | **4+3+3 (10 = n+4)** | 0..2 | 63 s |

The 3-type anatomy of the 2026 additive-chores counterexample does not
transplant to goods at any of these sizes/bounds, including the m = n+4
frontier for six agents — a size where the flat encoding (6^10 clauses)
is unthinkable.

## C. Local rigidity of the best near-miss

Ball-CEGAR (`efx/polish.py`) around the (4,11) near-miss V* (12 EFX
survivors, all slack 1; survivors = 3 rotation patterns × 4 free placements
of the epsilon-good g0): at lattice refinements ×10 and ×100 and L∞ radii
up to ~10% per entry, CP-SAT proves **no integer matrix in the ball kills
even the 12 known survivors** (INFEASIBLE on the kill-clause subset ⇒
certificate).  The neighborhood is locked by the epsilon-good rotation
family — the classic "one nearly-irrelevant good" degree of freedom — which
redirects future hunts toward instances where every good is pivotal.

## D. Hypothesis tests (annealing)

The "Archimedean middle" restriction (all values in [M, 2M)) was tested
and the prediction was that it *hurts*: with ratios < 2 a bundle S is
strongly envied only if |S| ≤ 2|T|−2, so singletons are never strongly
envied and balanced allocations are nearly unkillable.  Results confirmed
the prediction decisively — restricting to comparable magnitudes makes
instances *worse* by orders of magnitude, so epsilon-goods (mixed scales)
are structurally necessary for any counterexample:

| config | best #EFX (constrained) | unconstrained baseline |
|--------|--------------------------|------------------------|
| (4,10), values ∈ [64,127] | 2,997 | 591 |
| (4,11), values ∈ [64,127] | **17,811** | **12** |

Typed SA slices probe the m = 12–15 shapes heuristically at B = 1000, far
beyond the exact runs' value bounds (results below).

## Integer CP-SAT delta measurements

The positivity skeleton + monotone families — decisive over the reals —
slow the *integer* CP-SAT encoder ~4× ((4,7) B=2: 5.4→25 s; (4,8) B=2:
33→140 s), so they stay flag-gated off for integer runs.  The support-≥4
lemma joined the (4,8) B=3 integer attempt instead (run `frontier_4x8_B3_support4`).
