# Searching for a counterexample to EFX existence (additive valuations)

This repository is a computational attack on an **open problem** in fair
division, prompted by a "verifiable open problems" site task: exhibit an
n×m nonnegative-integer valuation matrix (n ≥ 4 agents, additive valuations)
such that **no** allocation of the m goods is EFX, with n^m small enough to
brute-force.

An allocation (A_1..A_n) is **EFX** iff for every ordered pair i ≠ j and every
good g ∈ A_j with V[i][g] > 0:  v_i(A_i) ≥ v_i(A_j) − V[i][g].

## Status of the problem

- EFX allocations exist for n ≤ 3 additive agents (Chaudhury–Garg–Mehlhorn,
  EC 2020), for m ≤ n+3 goods (Mahara), for bivalued instances, identical
  valuations, and several other special classes. Existence for n ≥ 4 additive
  agents is open and is one of the best-known open questions in fair division.
- In 2026, EFX existence was refuted for **monotone (and even submodular)**
  valuations via SAT solving ([arXiv:2604.18216](https://arxiv.org/abs/2604.18216)):
  counterexamples exist for n ≥ 3 agents and m ≥ n+5 items. That construction
  relies on complementarities that additivity forbids; the additive case is
  explicitly left open there. This repo ports the SAT methodology to the
  additive case.

So: a submission-sized additive counterexample would settle a famous open
problem. Expected outcome is negative certificates, and that is what
`REPORT.md` records precisely.

## Layout

- `efx/verifier.c` — exhaustive DFS over all n^m allocations with a
  proven-sound pruning rule (header comment has the proof), a margin
  parameter τ, plain-EF mode, and collection of surviving allocations.
  Builds as both a CLI (`efx_verify`) and a shared library for ctypes.
- `efx/reference.py` — slow numpy/pure-python transcriptions of the
  definition, used only to cross-validate the C code.
- `efx/crosscheck.py` — agreement suite (`make test`).
- `efx/encode.py` — CP-SAT encoding of "∃V ∀allocations ¬EFX" with shared
  violation literals (n·3^m, not n^m), half-reification, double-lex symmetry
  breaking, and individually-proved domain restrictions (docstring has the
  soundness arguments).
- `efx/solve.py` — `controls` (fixed-V consistency between encoder and
  verifier, EF SAT control, theorem UNSAT controls), `eager`, `cegar`.
- `efx/search.py` — simulated annealing minimizing the number of EFX
  allocations, evaluated through the C verifier (flat and typed modes,
  optional lower value bound).
- `efx/smt_encode.py` — QF_LRA SMT-LIB2 emitter (value-bound-free real
  certificates), z3/cvc5 runners, structural checker, mutation gates; the
  committed `efx/smt/*.smt2` files are the theorem objects.
- `efx/typed.py` — typed-goods collapse (t good types with multiplicities):
  count-matrix verifier with the exact multinomial-weighted count identity,
  CP-SAT encoder reaching m = 12–15 exactly.
- `efx/polish.py` — ball-CEGAR around a near-miss at refined lattice
  scales; produces counterexamples or local-rigidity certificates.
- `efx/runs/` — one JSON record per run (committed).
- `efx/candidates/` — near-misses; a confirmed counterexample would land
  here in the site's JSON format.

## Reproduce

```
make            # builds efx_verify and efx/efx.so
make test       # cross-validation suite
python3 efx/solve.py controls
python3 efx/solve.py eager --n 4 --m 8 --B 3 --time 600 --tag frontier_4x8_B3
python3 efx/search.py --n 4 --m 10 --seconds 420 --seed 1
```

Requires gcc, python3, numpy, ortools.
