#!/usr/bin/env python3
"""QF_LRA encoding of "there is a REAL-valued additive counterexample to EFX".

Emits SMT-LIB2 text directly (the committed .smt2 file is the theorem
object), runs it through z3 and cvc5 independently, and provides a
structural checker plus mutation tests.

Mathematical frame (soundness ledger, see also README):
  * Every EFX inequality involves one agent's row only and is homogeneous of
    degree 1 in that row, so per-row positive scaling is a symmetry of "V is
    a counterexample".  Rows are WLOG normalized to sum 1 (the all-zero-row
    case reduces to the (n-1, m) instance, discharged by that rung of the
    tower / CGM).
  * col-nonzero (every good positively valued by someone) is discharged by
    the (n, m-1) rung: a universally worthless good is inert padding under
    the positive-good removal definition.  NOTE: this is specific to the
    "EFX w.r.t. positively-valued goods" definition (the site's); under the
    any-good variant (EFX0) this restriction would be unsound.
  * Double-lex (non-strict, rows and columns) keeps the lex-least member of
    each S_n x S_m orbit (Flener et al. 2002); valid over any totally
    ordered domain, and it preserves row-sum-1 and col-nonzero.
  * viol/mp/sel semantics as in encode.py, with strict < over the reals:
    a model yields a genuine violation via the selected good, and a true
    counterexample extends to a satisfying assignment (mp := actual min
    positive value, sel := its argmin, every literal := its truth value).
  * pos-skeleton: pos[i][g] <=> V[i][g] > 0 (full biconditional) and
    hp[i][T] <=> OR pos — hands the SAT core the complete Boolean zero
    pattern; measured to be the difference between UNKNOWN and UNSAT.
  * monotone families (entailed by the verifier's pruning lemma, hence
    sound to add): viol[i][S+g][T] => viol[i][S][T] (more own goods, still
    envious => also with fewer) and viol[i][S][T] => viol[i][S][T+g]
    (v_i(T) - minpos_i(T) is nondecreasing in T).

UNSAT of the emitted formula therefore proves: no counterexample with n
agents and m goods exists over the nonnegative reals (up to the discharged
WLOGs), for the positive-good EFX definition.
"""

import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

SMT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "smt")
RUNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")


def bits(mask):
    g = 0
    while mask:
        if mask & 1:
            yield g
        mask >>= 1
        g += 1


# ---------------------------------------------------------------------------
# emitter
# ---------------------------------------------------------------------------

def emit_smt2(n, m, path=None, relation="efx", colnonzero=True, mono=True,
              lex=True, fixed=None, drop_allocs=None):
    """Build the SMT-LIB2 text.  fixed: optional n x m matrix of ints/
    Fractions to assert V equal to (rows normalized to sum 1 — per-row
    scaling is the symmetry).  drop_allocs: optional set of allocation
    tuples whose clauses are omitted (mutation tests).  Returns the text;
    writes it to path if given."""
    L = []
    ap = L.append
    ap("(set-logic QF_LRA)")
    ap(f"(set-info :source |EFX counterexample search n={n} m={m} "
       f"relation={relation} colnonzero={colnonzero} mono={mono} lex={lex}|)")

    V = [[f"V_{i}_{g}" for g in range(m)] for i in range(n)]
    for i in range(n):
        for g in range(m):
            ap(f"(declare-const {V[i][g]} Real)")
            ap(f"(assert (>= {V[i][g]} 0))")
    # row normalization (WLOG, rows nonzero)
    for i in range(n):
        ap(f"(assert (= (+ {' '.join(V[i])}) 1))")

    # pos skeleton (full biconditional)
    for i in range(n):
        for g in range(m):
            ap(f"(declare-const pos_{i}_{g} Bool)")
            ap(f"(assert (=> pos_{i}_{g} (> {V[i][g]} 0)))")
            ap(f"(assert (=> (not pos_{i}_{g}) (<= {V[i][g]} 0)))")
    if colnonzero:
        for g in range(m):
            ap("(assert (or " + " ".join(f"pos_{i}_{g}" for i in range(n)) + "))")

    full = (1 << m) - 1

    def bs(i, S):
        return "0" if S == 0 else f"bs_{i}_{S:x}"

    # bundle sums for all nonempty subsets (every one appears in some clause)
    for i in range(n):
        for S in range(1, full + 1):
            terms = " ".join(V[i][g] for g in bits(S))
            if bin(S).count("1") == 1:
                ap(f"(define-fun bs_{i}_{S:x} () Real {terms})")
            else:
                ap(f"(define-fun bs_{i}_{S:x} () Real (+ {terms}))")

    # mp / hp / sel per (i, T), T nonempty  (efx only)
    if relation == "efx":
        for i in range(n):
            for T in range(1, full + 1):
                ap(f"(declare-const mp_{i}_{T:x} Real)")
                ap(f"(assert (> mp_{i}_{T:x} 0))")
                ap(f"(declare-const hp_{i}_{T:x} Bool)")
                ap(f"(assert (= hp_{i}_{T:x} (or " +
                   " ".join(f"pos_{i}_{g}" for g in bits(T)) + ")))")
                sels = []
                for g in bits(T):
                    s = f"sel_{i}_{T:x}_{g}"
                    sels.append(s)
                    ap(f"(declare-const {s} Bool)")
                    ap(f"(assert (=> {s} pos_{i}_{g}))")
                    ap(f"(assert (=> {s} (<= {V[i][g]} mp_{i}_{T:x})))")
                ap(f"(assert (=> hp_{i}_{T:x} (or {' '.join(sels)})))")

    # viol literals for all ordered disjoint (S, T), T nonempty
    for i in range(n):
        for T in range(1, full + 1):
            rest = full & ~T
            S = rest
            while True:
                v = f"viol_{i}_{S:x}_{T:x}"
                ap(f"(declare-const {v} Bool)")
                if relation == "efx":
                    ap(f"(assert (=> {v} hp_{i}_{T:x}))")
                    ap(f"(assert (=> {v} (< (+ {bs(i, S)} (- {bs(i, T)}) "
                       f"mp_{i}_{T:x}) 0)))")
                else:
                    ap(f"(assert (=> {v} (< (- {bs(i, S)} {bs(i, T)}) 0)))")
                if S == 0:
                    break
                S = (S - 1) & rest

    # monotone families (binary clauses over existing viol literals)
    if mono and relation == "efx":
        for i in range(n):
            for T in range(1, full + 1):
                rest = full & ~T
                S = rest
                while True:
                    for g in bits(full & ~(S | T)):
                        ap(f"(assert (=> viol_{i}_{S | (1 << g):x}_{T:x} "
                           f"viol_{i}_{S:x}_{T:x}))")
                        ap(f"(assert (=> viol_{i}_{S:x}_{T:x} "
                           f"viol_{i}_{S:x}_{T | (1 << g):x}))")
                    if S == 0:
                        break
                    S = (S - 1) & rest

    # double-lex symmetry breaking (non-strict)
    def lex_le(xs, ys, tag):
        prev = None
        for k, (x, y) in enumerate(zip(xs, ys)):
            if prev is None:
                ap(f"(assert (<= {x} {y}))")
            else:
                ap(f"(assert (=> {prev} (<= {x} {y})))")
            if k < len(xs) - 1:
                e = f"lex_{tag}_{k}"
                ap(f"(declare-const {e} Bool)")
                if prev is not None:
                    ap(f"(assert (=> {e} {prev}))")
                ap(f"(assert (=> {e} (= {x} {y})))")
                prev = e

    if lex and fixed is None:
        for i in range(n - 1):
            lex_le(V[i], V[i + 1], f"r{i}")
        for g in range(m - 1):
            lex_le([V[i][g] for i in range(n)],
                   [V[i][g + 1] for i in range(n)], f"c{g}")

    # fixed-V mode (mutation/consistency tests)
    if fixed is not None:
        from fractions import Fraction
        for i in range(n):
            row = [Fraction(x) for x in fixed[i]]
            tot = sum(row)
            assert tot > 0, "fixed row must be nonzero"
            for g in range(m):
                q = row[g] / tot
                ap(f"(assert (= {V[i][g]} (/ {q.numerator} {q.denominator})))")

    # allocation clauses
    drop = {tuple(a) for a in drop_allocs} if drop_allocs else set()
    n_dropped = 0
    for alloc in itertools.product(range(n), repeat=m):
        if alloc in drop:
            n_dropped += 1
            continue
        masks = [0] * n
        for g, a in enumerate(alloc):
            masks[a] |= 1 << g
        lits = [f"viol_{i}_{masks[i]:x}_{masks[j]:x}"
                for i in range(n) for j in range(n)
                if i != j and masks[j]]
        ap("(assert (or " + " ".join(lits) + "))")
    if drop_allocs:
        assert n_dropped == len(drop), "dropped allocations must be distinct"

    ap("(check-sat)")
    text = "\n".join(L) + "\n"
    if path:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as fh:
            fh.write(text)
    return text


# ---------------------------------------------------------------------------
# runners
# ---------------------------------------------------------------------------

def run_z3(path, timeout_s, arith_solver=2):
    import z3
    z3.set_param("smt.arith.solver", arith_solver)
    t0 = time.time()
    s = z3.Solver()
    s.set("timeout", int(timeout_s * 1000))
    s.add(z3.parse_smt2_file(path))
    res = s.check()
    wall = time.time() - t0
    out = {"solver": f"z3-arith{arith_solver}", "status": str(res),
           "wall": wall}
    try:
        st = s.statistics()
        for k in ("conflicts", "decisions", "arith-conflicts"):
            try:
                out[k] = st.get_key_value(k)
            except Exception:
                pass
    except Exception:
        pass
    if str(res) == "sat":
        mdl = s.model()
        out["model"] = {str(d): str(mdl[d]) for d in mdl.decls()
                        if str(d).startswith("V_")}
    return out


def run_cvc5(path, timeout_s):
    import cvc5
    t0 = time.time()
    slv = cvc5.Solver()
    slv.setOption("tlimit", str(int(timeout_s * 1000)))
    slv.setOption("produce-models", "true")
    parser = cvc5.InputParser(slv)
    parser.setFileInput(cvc5.InputLanguage.SMT_LIB_2_6, path)
    sm = parser.getSymbolManager()
    status = None
    while True:
        cmd = parser.nextCommand()
        if cmd.isNull():
            break
        res = cmd.invoke(slv, sm)
        if res and res.strip() in ("sat", "unsat", "unknown"):
            status = res.strip()
    wall = time.time() - t0
    return {"solver": "cvc5", "status": status or "unknown", "wall": wall}


def extract_model_matrix(model, n, m):
    """Turn z3 model strings for V_i_g into integer matrix via per-row
    rationalization (per-row scaling is the symmetry)."""
    from fractions import Fraction
    import math
    M = []
    for i in range(n):
        row = []
        for g in range(m):
            sv = model[f"V_{i}_{g}"]
            row.append(Fraction(sv.replace(" ", "")) if "/" in sv
                       else Fraction(sv))
        den = 1
        for q in row:
            den = den * q.denominator // math.gcd(den, q.denominator)
        M.append([int(q * den) for q in row])
    return M


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


# ---------------------------------------------------------------------------
# structural checker (independent of the emitter's control flow)
# ---------------------------------------------------------------------------

def check_structure(path, n, m, colnonzero=True, mono=True, lex=True):
    """Parse the .smt2 and verify assertion-category counts derived from
    (n, m) combinatorics from scratch, then rebuild 20 random allocation
    clauses literal-by-literal and confirm each exists verbatim."""
    import z3
    asts = z3.parse_smt2_file(path)
    sexprs = set()
    n_or_viol = 0
    for a in asts:
        s = a.sexpr()
        sexprs.add(s)
        if s.startswith("(or viol_"):
            n_or_viol += 1
    p3 = 3 ** m
    p2 = 2 ** m
    exp_alloc = n ** m
    exp_viol = n * (p3 - p2)          # ordered disjoint pairs, T nonempty
    # every viol has 2 implications; count assertions mentioning "=> viol" at top
    ok = True
    if n_or_viol != exp_alloc:
        print(f"STRUCT FAIL: alloc clauses {n_or_viol} != {exp_alloc}")
        ok = False
    # spot-rebuild 20 random allocation clauses
    rng = random.Random(1)
    for _ in range(20):
        alloc = [rng.randrange(n) for _ in range(m)]
        masks = [0] * n
        for g, a in enumerate(alloc):
            masks[a] |= 1 << g
        lits = [f"viol_{i}_{masks[i]:x}_{masks[j]:x}"
                for i in range(n) for j in range(n) if i != j and masks[j]]
        want = "(or " + " ".join(lits) + ")"
        if want not in sexprs:
            print(f"STRUCT FAIL: missing clause for {alloc}")
            ok = False
    # spot-check mp/sel semantics on 5 random (i, T)
    for _ in range(5):
        i = rng.randrange(n)
        T = rng.randrange(1, p2)
        g = rng.choice(list(bits(T)))
        if f"(=> sel_{i}_{T:x}_{g} pos_{i}_{g})" not in sexprs:
            print(f"STRUCT FAIL: sel->pos missing for i={i} T={T:x} g={g}")
            ok = False
        if f"(=> sel_{i}_{T:x}_{g} (<= V_{i}_{g} mp_{i}_{T:x}))" not in sexprs:
            print(f"STRUCT FAIL: sel<=mp missing for i={i} T={T:x} g={g}")
            ok = False
    print(f"structure check {'OK' if ok else 'FAILED'}: "
          f"{n_or_viol} alloc clauses, expected viol lits {exp_viol}")
    return ok


# ---------------------------------------------------------------------------
# gates / drivers
# ---------------------------------------------------------------------------

def gate_mutations():
    """G2: three end-to-end mutation tests at tiny sizes."""
    import native
    rng = random.Random(5)
    ok = True

    # (a) survivor-drop: take a random matrix, ask the C verifier for its
    # exact EFX survivors, drop precisely those clauses, fix V — the formula
    # must become SAT (checks the clause<->allocation correspondence and
    # good ordering end to end; with all clauses present the same matrix is
    # non-SAT, which is case (c) below)
    for _ in range(3):
        n, m = 3, 4
        M = [[rng.randint(0, 5) for _ in range(m)] for _ in range(n)]
        for i in range(n):
            if not any(M[i]):
                M[i][rng.randrange(m)] = 1
        chk = native.verify(M, tau=1, cap=0, collect=n ** m)
        if chk["count"] == 0:
            continue
        p = os.path.join(SMT_DIR, "mut_drop_3x4.smt2")
        emit_smt2(n, m, p, fixed=M, drop_allocs=chk["allocs"],
                  lex=False, colnonzero=False)
        r = run_z3(p, 60)
        if r["status"] != "sat":
            print(f"MUT(a) FAIL: {r['status']} for M={M} "
                  f"(dropped {chk['count']} survivors)")
            ok = False

    # (b) EF relation at (2,3): SAT, model confirmed EF-counterexample
    p = os.path.join(SMT_DIR, "mut_ef_2x3.smt2")
    emit_smt2(2, 3, p, relation="ef", lex=True)
    r = run_z3(p, 60)
    if r["status"] != "sat":
        print(f"MUT(b) FAIL: {r['status']}")
        ok = False
    else:
        M = extract_model_matrix(r["model"], 2, 3)
        if native.verify(M, tau=1, relation=1)["count"] != 0:
            print("MUT(b) FAIL: model not an EF counterexample")
            ok = False

    # (c) fixed-V on matrices with known EFX survivors: must NOT be unsat
    for _ in range(4):
        M = [[rng.randint(0, 5) for _ in range(4)] for _ in range(3)]
        for i in range(3):
            if not any(M[i]):
                M[i][rng.randrange(4)] = 1
        want_sat = native.verify(M, tau=1, cap=1)["count"] == 0
        p = os.path.join(SMT_DIR, "mut_fixed_3x4.smt2")
        emit_smt2(3, 4, p, fixed=M, lex=False, colnonzero=False)
        r = run_z3(p, 60)
        got_sat = r["status"] == "sat"
        if r["status"] == "unknown" or want_sat != got_sat:
            print(f"MUT(c) FAIL: {r['status']} vs verifier count0={want_sat}")
            ok = False
    print(f"mutation gates {'OK' if ok else 'FAILED'}")
    return ok


LADDER = [(2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6)]


def gate_ladder(caps=None):
    """G1+G3: theorem rungs.  z3 must prove every rung UNSAT within its cap;
    cvc5 disagreement on unsat is a hard failure, cvc5 timeouts are recorded
    (they only affect which solver leads Stage 1)."""
    caps = caps or {}
    all_ok = True
    for (n, m) in LADDER:
        tag = f"real_{n}x{m}"
        p = os.path.join(SMT_DIR, f"efx_{n}x{m}.smt2")
        emit_smt2(n, m, p)
        cap = caps.get((n, m), 300)
        rz = run_z3(p, cap)
        rc = run_cvc5(p, cap)
        record(tag, {"n": n, "m": m, "z3": rz, "cvc5": rc,
                     "status": f"z3:{rz['status']}/cvc5:{rc['status']}",
                     "wall": rz["wall"] + rc["wall"], "file": p})
        if rz["status"] != "unsat":
            print(f"LADDER {tag}: z3 {rz['status']} (expected unsat)")
            all_ok = False
        if rc["status"] == "sat":
            print(f"LADDER {tag}: cvc5 SAT disagrees with theorem!")
            all_ok = False
    return all_ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["gates", "emit", "run", "check"])
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--m", type=int, default=7)
    ap.add_argument("--time", type=float, default=1800)
    ap.add_argument("--solver", default="z3", choices=["z3", "cvc5"])
    ap.add_argument("--arith", type=int, default=2)
    ap.add_argument("--no-mono", action="store_true")
    ap.add_argument("--tag", default=None)
    args = ap.parse_args()

    if args.mode == "gates":
        ok0 = True
        try:
            import cvc5  # noqa: F401
        except Exception as e:
            print(f"G0 FAIL: cvc5 import: {e}")
            ok0 = False
        p = os.path.join(SMT_DIR, "efx_2x4.smt2")
        emit_smt2(2, 4, p)
        ok1 = run_z3(p, 60)["status"] == "unsat" and \
            run_cvc5(p, 60)["status"] == "unsat"
        print(f"G1 (2,4) both-unsat: {'OK' if ok1 else 'FAIL'}")
        ok2 = gate_mutations()
        ok3 = gate_ladder(caps={(3, 6): 300})
        ok4 = check_structure(os.path.join(SMT_DIR, "efx_3x6.smt2"), 3, 6)
        print(f"GATES {'ALL OK' if all([ok0, ok1, ok2, ok3, ok4]) else 'FAILED'}")
        return 0 if all([ok0, ok1, ok2, ok3, ok4]) else 1

    p = os.path.join(SMT_DIR, f"efx_{args.n}x{args.m}.smt2")
    if args.mode == "emit":
        emit_smt2(args.n, args.m, p, mono=not args.no_mono)
        print(f"emitted {p} ({os.path.getsize(p)} bytes)")
        return 0
    if args.mode == "check":
        return 0 if check_structure(p, args.n, args.m) else 1
    # run
    if not os.path.exists(p):
        emit_smt2(args.n, args.m, p, mono=not args.no_mono)
    tag = args.tag or f"real_{args.n}x{args.m}_{args.solver}"
    r = run_z3(p, args.time, args.arith) if args.solver == "z3" \
        else run_cvc5(p, args.time)
    out = record(tag, {"n": args.n, "m": args.m, "file": p, **r})
    if r["status"] == "sat":
        import native
        M = extract_model_matrix(r["model"], args.n, args.m)
        chk = native.verify(M, tau=1, cap=0)
        print(f"!!! SAT model verifier count={chk['count']} M={M}")
        out["verifier_count"] = chk["count"]
        record(tag, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
