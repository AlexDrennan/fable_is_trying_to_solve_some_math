"""CP-SAT encoding of "there is a valuation matrix with NO EFX allocation".

Existential side: integer variables V[i][g] in [lo, B].  Universal side: one
clause per allocation saying "some ordered agent pair violates EFX here".

The violation literal viol[i][S][T] ("agent i, holding bundle S, strongly
envies bundle T even after removing T's least positive good") depends only on
(i, S, T), so there are at most n * 3^m of them, shared across all n^m
allocation clauses.  Structure per (i, T):
    mp[i][T]      int in [1, B]
    haspos[i][T]  bool
    sel[i][T][g]  bool for g in T, with
        haspos => OR_g sel,   sel_g => V[i][g] >= 1,   sel_g => V[i][g] <= mp
    viol[i][S][T] => haspos[i][T]
    viol[i][S][T] => bsum[i][S] - bsum[i][T] + mp[i][T] <= -1
Everything is half-reified (OnlyEnforceIf), which is sound in both directions:

  * SAT direction: if viol is true then some selected g has V[i][g] >= 1 and
    V[i][g] <= mp, so bsum_S - bsum_T + V[i][g] <= bsum_S - bsum_T + mp <= -1,
    i.e. a genuine EFX violation via g.  Hence a model's matrix genuinely
    kills every encoded allocation (and is re-verified externally anyway).
  * UNSAT direction: a true counterexample extends to a satisfying assignment
    (set every literal to its actual truth value, mp to the actual min
    positive value — the argmin works simultaneously for every S — and
    canonicalize under the symmetry-breaking below).  So UNSAT proves no
    counterexample exists in the searched class.

Symmetry breaking (soundness: agents and goods are fully interchangeable, and
every matrix orbit under S_n x S_m contains a member whose rows and columns
are simultaneously lex-nondecreasing — Flener et al. 2002): non-strict lex
chains on adjacent rows and adjacent columns.  Rows must NOT be strict:
distinct agents may share a row (only the all-identical case is a theorem).

Optional restrictions (each individually proved sound for goods/EFX):
  * row_nonzero: an agent with an all-zero row can be given the empty bundle
    and the rest allocated EFX among the other n-1 <= 3 agents (CGM 2020);
    the empty bundle triggers no condition in either direction.
  * col_nonzero: a good worth 0 to everyone can be added to any bundle of an
    EFX allocation of the remaining goods (it adds 0 and is never removable
    under the positive-good definition).
  * support4 (n = 4 only): if agent i values <= 3 goods positively, give i its
    single most valuable good g1 and allocate the rest EFX among the other
    three (CGM).  Nobody strongly envies {g1} (removing g1 empties it), and
    each rival bundle contains <= 2 of i's positive goods, so
    v_i(A_j) - minpos_i(A_j) <= max single value <= v_i({g1}).
"""

from ortools.sat.python import cp_model


def bits(mask):
    g = 0
    while mask:
        if mask & 1:
            yield g
        mask >>= 1
        g += 1


class EFXEncoder:
    def __init__(self, n, m, B, lo=0, relation="efx"):
        assert B >= 1 and 0 <= lo <= B
        self.n, self.m, self.B, self.lo = n, m, B, lo
        self.relation = relation
        self.model = cp_model.CpModel()
        self.V = [[self.model.NewIntVar(lo, B, f"V_{i}_{g}") for g in range(m)]
                  for i in range(n)]
        self._bsum = {}
        self._mp = {}
        self._viol = {}
        self._pos = None
        self.clauses = 0

    # -- lazily created shared structure ------------------------------------
    def pos(self):
        if self._pos is None:
            self._pos = [[self.model.NewBoolVar(f"pos_{i}_{g}")
                          for g in range(self.m)] for i in range(self.n)]
            for i in range(self.n):
                for g in range(self.m):
                    p = self._pos[i][g]
                    self.model.Add(self.V[i][g] >= 1).OnlyEnforceIf(p)
                    self.model.Add(self.V[i][g] <= 0).OnlyEnforceIf(p.Not())
        return self._pos

    def bsum(self, i, S):
        if S == 0:
            return 0
        key = (i, S)
        v = self._bsum.get(key)
        if v is None:
            v = self.model.NewIntVar(0, self.m * self.B, f"bs_{i}_{S:x}")
            self.model.Add(v == sum(self.V[i][g] for g in bits(S)))
            self._bsum[key] = v
        return v

    def mp_haspos(self, i, T):
        key = (i, T)
        r = self._mp.get(key)
        if r is None:
            mp = self.model.NewIntVar(1, self.B, f"mp_{i}_{T:x}")
            hp = self.model.NewBoolVar(f"hp_{i}_{T:x}")
            sels = []
            for g in bits(T):
                sl = self.model.NewBoolVar(f"sel_{i}_{T:x}_{g}")
                self.model.Add(self.V[i][g] >= 1).OnlyEnforceIf(sl)
                self.model.Add(self.V[i][g] <= mp).OnlyEnforceIf(sl)
                sels.append(sl)
            self.model.AddBoolOr(sels).OnlyEnforceIf(hp)
            r = (mp, hp)
            self._mp[key] = r
        return r

    def viol(self, i, S, T):
        assert T != 0
        key = (i, S, T)
        v = self._viol.get(key)
        if v is None:
            v = self.model.NewBoolVar(f"viol_{i}_{S:x}_{T:x}")
            if self.relation == "efx":
                mp, hp = self.mp_haspos(i, T)
                self.model.AddImplication(v, hp)
                self.model.Add(self.bsum(i, S) - self.bsum(i, T) + mp
                               <= -1).OnlyEnforceIf(v)
            else:  # plain EF
                self.model.Add(self.bsum(i, S) - self.bsum(i, T)
                               <= -1).OnlyEnforceIf(v)
            self._viol[key] = v
        return v

    # -- allocation clauses --------------------------------------------------
    def add_alloc_clause(self, alloc):
        masks = [0] * self.n
        for g, a in enumerate(alloc):
            masks[a] |= 1 << g
        lits = []
        for i in range(self.n):
            for j in range(self.n):
                if i != j and masks[j]:
                    lits.append(self.viol(i, masks[i], masks[j]))
        self.model.AddBoolOr(lits)
        self.clauses += 1

    def add_all_allocs(self):
        n, m = self.n, self.m
        alloc = [0] * m
        while True:
            self.add_alloc_clause(alloc)
            d = 0
            while d < m and alloc[d] == n - 1:
                alloc[d] = 0
                d += 1
            if d == m:
                break
            alloc[d] += 1

    # -- symmetry breaking and restrictions ---------------------------------
    def _lex_le(self, xs, ys):
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

    def add_double_lex(self):
        for i in range(self.n - 1):
            self._lex_le(self.V[i], self.V[i + 1])
        for g in range(self.m - 1):
            self._lex_le([self.V[i][g] for i in range(self.n)],
                         [self.V[i][g + 1] for i in range(self.n)])

    def add_row_col_nonzero(self):
        pos = self.pos()
        for i in range(self.n):
            self.model.AddBoolOr(pos[i])
        for g in range(self.m):
            self.model.AddBoolOr([pos[i][g] for i in range(self.n)])

    def add_support_at_least(self, k):
        pos = self.pos()
        for i in range(self.n):
            self.model.Add(sum(pos[i]) >= k)

    def fix_values(self, Vc):
        for i in range(self.n):
            for g in range(self.m):
                self.model.Add(self.V[i][g] == int(Vc[i][g]))

    # -- solving -------------------------------------------------------------
    def solve(self, time_limit=60.0, workers=4, seed=0, hint=None,
              log_file=None):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(time_limit)
        solver.parameters.num_workers = int(workers)
        solver.parameters.random_seed = int(seed)
        if hint is not None:
            for i in range(self.n):
                for g in range(self.m):
                    self.model.AddHint(self.V[i][g], int(hint[i][g]))
        if log_file:
            solver.parameters.log_search_progress = True
            with open(log_file, "w") as fh:
                solver.log_callback = fh.write  # pragma: no cover
                status = solver.Solve(self.model)
        else:
            status = solver.Solve(self.model)
        name = solver.StatusName(status)
        out = {"status": name,
               "wall": solver.WallTime(),
               "conflicts": solver.NumConflicts(),
               "branches": solver.NumBranches()}
        if name in ("FEASIBLE", "OPTIMAL"):
            out["V"] = [[int(solver.Value(self.V[i][g]))
                         for g in range(self.m)] for i in range(self.n)]
        return out
