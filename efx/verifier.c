/*
 * verifier.c — exhaustive checker for existence of EFX allocations under
 * additive valuations, with a margin parameter tau and a plain-EF mode.
 *
 * Definition checked (tau = 1, relation = 0 = EFX), matching the task
 * statement verbatim: an allocation (A_0..A_{n-1}) of m goods to n agents is
 * EFX iff for every ordered pair of agents i != j and every good g in A_j
 * with V[i][g] > 0:
 *      v_i(A_i) >= v_i(A_j) - V[i][g],      v_i(S) = sum_{g in S} V[i][g].
 * Only positively-valued goods are removable; a bundle containing no good
 * that i values positively imposes no (i,j) constraint.
 *
 * With minpos_i(T) = min{ V[i][g] : g in T, V[i][g] > 0 } (undefined if none)
 * and f_{i,j} = v_i(A_j) - minpos_i(A_j), the allocation "survives at margin
 * tau" iff f_{i,j} - v_i(A_i) < tau for every pair where f is defined.
 * tau = 1 is exactly EFX for integer inputs; larger tau asks for slack.
 * relation = 1 (EF) uses f_{i,j} = v_i(A_j) instead (defined for all pairs).
 *
 * Pruning (proved sound): for a fixed pair (i,j), f_{i,j} never decreases as
 * goods are added to A_j — adding a good of i-value x to (v, mp): if x >= mp
 * then (v+x) - mp >= v - mp; if 0 < x < mp then (v+x) - x = v >= v - mp; if
 * x = 0 nothing changes; the first positive good moves f from "undefined"
 * (no constraint) to (v+x) - x = v.  Meanwhile v_i(A_i) can grow by at most
 * rem[i], i's total value of the still-unassigned goods.  Hence if
 * f_{i,j} - (v_i(A_i) + rem[i]) >= tau at a partial assignment, no completion
 * survives, and the subtree can be cut.  At a leaf rem = 0, so the same test
 * is the exact survival check.  The EF variant uses the same argument with
 * f = v_i(A_j), which is also nondecreasing.
 *
 * The DFS state (bundle sums, per-bundle min-positive, remaining values) is
 * copied down the stack rather than undone on backtrack, because the min of a
 * bundle cannot be restored after removal without extra bookkeeping.
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 6
#define MAXM 16

#define MP_NONE INT64_MAX                       /* bundle has no positive good */
#define SLACK_UTOPIA ((int64_t)1 << 40)         /* slack of an unconstrained leaf */
#define SUM_SAT ((int64_t)1 << 60)              /* saturation for sum_slack */

typedef struct {
    int64_t count;      /* surviving allocations found (up to cap) */
    int64_t nodes;      /* DFS nodes visited */
    int64_t min_slack;  /* min over surviving leaves of min pair slack; INT64_MAX if count = 0 */
    int64_t sum_slack;  /* saturating sum of per-leaf slack over survivors */
    int32_t aborted;    /* 1 iff stopped early because count reached cap */
    int32_t _pad;
} EfxResult;

typedef struct {
    int64_t s[MAXN][MAXN];   /* s[i][a] = v_i(A_a) */
    int64_t mp[MAXN][MAXN];  /* min positive V[i][g] over g in A_a; MP_NONE if none */
    int64_t rem[MAXN];       /* i's total value of unassigned goods */
} State;

typedef struct {
    int n, m, relation;
    int64_t tau, cap;
    int64_t V[MAXN][MAXM];   /* values in DFS good order (sorted) */
    int orig[MAXM];          /* orig[d] = original index of DFS good d */
    uint8_t assign[MAXM];    /* current partial assignment, DFS order */
    uint8_t *allocs;         /* out buffer, max_allocs * m, ORIGINAL good order */
    int64_t max_allocs;
    EfxResult r;
} Ctx;

static void leaf(Ctx *c, const State *st)
{
    int n = c->n;
    int64_t worst = INT64_MIN; /* max over defined pairs of f - v_i(A_i) */
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (i == j) continue;
            int64_t f;
            if (c->relation == 0) {
                if (st->mp[i][j] == MP_NONE) continue;
                f = st->s[i][j] - st->mp[i][j];
            } else {
                f = st->s[i][j];
            }
            int64_t d = f - st->s[i][i];
            if (d > worst) worst = d;
        }
    }
    if (worst != INT64_MIN && worst >= c->tau) return; /* violated */

    c->r.count++;
    int64_t slack = (worst == INT64_MIN) ? SLACK_UTOPIA : -worst;
    if (slack < c->r.min_slack) c->r.min_slack = slack;
    if (c->r.sum_slack < SUM_SAT - slack) c->r.sum_slack += slack;
    else c->r.sum_slack = SUM_SAT;
    if (c->allocs && c->r.count <= c->max_allocs) {
        uint8_t *row = c->allocs + (size_t)(c->r.count - 1) * (size_t)c->m;
        for (int d = 0; d < c->m; d++) row[c->orig[d]] = c->assign[d];
    }
    if (c->r.count >= c->cap) c->r.aborted = 1;
}

static void dfs(Ctx *c, int depth, const State *st)
{
    c->r.nodes++;
    if (depth == c->m) { leaf(c, st); return; }
    int n = c->n;

    /* try agents in descending order of their value for this good: finds a
       surviving witness earlier in easy instances; order does not affect
       count/min/sum, which range over all leaves */
    int order[MAXN];
    for (int a = 0; a < n; a++) order[a] = a;
    for (int a = 1; a < n; a++) {
        int t = order[a], b = a;
        while (b > 0 && c->V[order[b - 1]][depth] < c->V[t][depth]) {
            order[b] = order[b - 1];
            b--;
        }
        order[b] = t;
    }

    for (int oi = 0; oi < n; oi++) {
        int a = order[oi];
        State ns = *st;
        for (int i = 0; i < n; i++) {
            int64_t x = c->V[i][depth];
            ns.rem[i] -= x;
            ns.s[i][a] += x;
            if (x > 0 && x < ns.mp[i][a]) ns.mp[i][a] = x;
        }
        int dead = 0;
        for (int i = 0; i < n && !dead; i++) {
            int64_t lhs = ns.s[i][i] + ns.rem[i];
            for (int j = 0; j < n; j++) {
                if (i == j) continue;
                int64_t f;
                if (c->relation == 0) {
                    if (ns.mp[i][j] == MP_NONE) continue;
                    f = ns.s[i][j] - ns.mp[i][j];
                } else {
                    f = ns.s[i][j];
                }
                if (f - lhs >= c->tau) { dead = 1; break; }
            }
        }
        if (!dead) {
            c->assign[depth] = (uint8_t)a;
            dfs(c, depth + 1, &ns);
            if (c->r.aborted) return;
        }
    }
}

/*
 * Returns 0 on success, negative on bad arguments.
 * V: row-major n*m nonnegative values.  cap <= 0 means unlimited.
 * relation: 0 = EFX, 1 = EF.  allocs (optional): buffer for the first
 * max_allocs surviving allocations, one byte per good, original good order.
 */
int efx_verify(int n, int m, const int64_t *V, int64_t tau, int64_t cap,
               int relation, EfxResult *out, uint8_t *allocs, int64_t max_allocs)
{
    if (n < 1 || n > MAXN || m < 1 || m > MAXM || !V || !out) return -1;
    if (tau < 0) return -1;
    for (int k = 0; k < n * m; k++)
        if (V[k] < 0) return -2;

    Ctx c;
    memset(&c, 0, sizeof c);
    c.n = n;
    c.m = m;
    c.relation = relation;
    c.tau = tau;
    c.cap = (cap <= 0) ? INT64_MAX : cap;
    c.allocs = allocs;
    c.max_allocs = allocs ? max_allocs : 0;
    c.r.min_slack = INT64_MAX;

    /* stable sort of goods by descending total value (better pruning) */
    int64_t tot[MAXM];
    int idx[MAXM];
    for (int g = 0; g < m; g++) {
        tot[g] = 0;
        idx[g] = g;
        for (int i = 0; i < n; i++) tot[g] += V[(size_t)i * m + g];
    }
    for (int a = 1; a < m; a++) {
        int t = idx[a], b = a;
        while (b > 0 && tot[idx[b - 1]] < tot[t]) {
            idx[b] = idx[b - 1];
            b--;
        }
        idx[b] = t;
    }
    for (int d = 0; d < m; d++) {
        c.orig[d] = idx[d];
        for (int i = 0; i < n; i++) c.V[i][d] = V[(size_t)i * m + idx[d]];
    }

    State st;
    memset(&st, 0, sizeof st);
    for (int i = 0; i < MAXN; i++)
        for (int j = 0; j < MAXN; j++) st.mp[i][j] = MP_NONE;
    for (int i = 0; i < n; i++) {
        st.rem[i] = 0;
        for (int g = 0; g < m; g++) st.rem[i] += V[(size_t)i * m + g];
    }

    dfs(&c, 0, &st);
    *out = c.r;
    return 0;
}

#ifdef EFX_MAIN
/*
 * CLI: efx_verify FILE [tau] [cap] [relation] [collect]
 * FILE: first line "n m", then n rows of m nonnegative integers.
 * Prints a one-line JSON result; with collect > 0 also prints up to that many
 * surviving allocations (agent id per good, original good order).
 */
int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "usage: %s FILE [tau=1] [cap=0] [relation=0] [collect=0]\n", argv[0]);
        return 2;
    }
    FILE *fp = fopen(argv[1], "r");
    if (!fp) { perror("fopen"); return 2; }
    int n, m;
    if (fscanf(fp, "%d %d", &n, &m) != 2) { fprintf(stderr, "bad header\n"); return 2; }
    if (n < 1 || n > MAXN || m < 1 || m > MAXM) { fprintf(stderr, "bad dims\n"); return 2; }
    int64_t *V = malloc(sizeof(int64_t) * (size_t)n * (size_t)m);
    for (int k = 0; k < n * m; k++)
        if (fscanf(fp, "%" SCNd64, &V[k]) != 1) { fprintf(stderr, "bad value\n"); return 2; }
    fclose(fp);

    int64_t tau = argc > 2 ? atoll(argv[2]) : 1;
    int64_t cap = argc > 3 ? atoll(argv[3]) : 0;
    int relation = argc > 4 ? atoi(argv[4]) : 0;
    int64_t collect = argc > 5 ? atoll(argv[5]) : 0;

    uint8_t *allocs = NULL;
    if (collect > 0) allocs = malloc((size_t)collect * (size_t)m);

    EfxResult r;
    int rc = efx_verify(n, m, V, tau, cap, relation, &r, allocs, collect);
    if (rc != 0) { fprintf(stderr, "efx_verify rc=%d\n", rc); return 2; }
    printf("{\"count\": %lld, \"nodes\": %lld, \"min_slack\": %lld, "
           "\"sum_slack\": %lld, \"aborted\": %d}\n",
           (long long)r.count, (long long)r.nodes, (long long)r.min_slack,
           (long long)r.sum_slack, (int)r.aborted);
    if (allocs) {
        int64_t k = r.count < collect ? r.count : collect;
        for (int64_t t = 0; t < k; t++) {
            for (int g = 0; g < m; g++)
                printf("%d%c", allocs[t * m + g], g + 1 == m ? '\n' : ' ');
        }
    }
    free(V);
    free(allocs);
    return 0;
}
#endif
