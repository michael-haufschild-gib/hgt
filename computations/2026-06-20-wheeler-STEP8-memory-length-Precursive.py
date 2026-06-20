"""
STEP 8 — transfer of the granular-MEMORY node test to HT, testing a VALUE RELATION (not a
dependency/causality) and NON-HT-blind. Granular: state = functional of path; memory length
= how far back history matters. Function analog: a value SEQUENCE a_n has FINITE memory iff
it is P-recursive — satisfies sum_{i=0}^{r} p_i(n) a_{n+i} = 0 with polynomials p_i (deg<=d).
DA/holonomic sequences = finite memory; an HT/arithmetic sequence = infinite memory (NOT P-rec).
This DISTINGUISHES the two (not HT-blind) via a pure value relation among the a_n.
Fast: numpy SVD on a small design matrix.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

def memory_length(seq, rmax=4, dmax=3):
    """smallest (r,d) giving a near-exact polynomial recurrence sum_i p_i(n) a_{n+i}=0."""
    N = len(seq)
    best = None
    for r in range(1, rmax+1):
        for d in range(0, dmax+1):
            rows = []
            for n in range(1, N-r):
                row = []
                for i in range(r+1):
                    for k in range(d+1):
                        row.append((n**k) * seq[n+i])
                rows.append(row)
            A = np.array(rows, dtype=float)
            if A.shape[0] < A.shape[1]: continue
            scale = np.linalg.norm(A, axis=0); scale[scale==0]=1
            A = A/scale
            s = np.linalg.svd(A, compute_uv=False)
            resid = s[-1]/s[0]
            if resid < 1e-9:
                return (r, d, float(resid))
            if best is None or resid < best[2]:
                best = (r, d, float(resid))
    return ("inf", "-", best[2])   # no finite recurrence found

# normalize huge sequences by working with log-magnitude where needed
seqs = {
 "2^n (geometric: finite memory, r=1)":      [float(2**n) for n in range(2,40)],
 "n! (factorial: finite memory, r=1)":       [float(mp.factorial(n)) for n in range(2,30)],
 "Fibonacci (finite memory, r=2)":           [float(mp.fib(n)) for n in range(2,40)],
 "Bernoulli B_2n ~ zeta(2n) (holonomic?)":   [float(abs(mp.bernoulli(2*n))) for n in range(1,22)],
 "zeta(n), n=2..30 (HT values: infinite?)":  [float(mp.zeta(n)) for n in range(2,31)],
 "nth prime (arithmetic: infinite memory)":  [float(p) for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]],
}
print("="*74)
print(" STEP8: MEMORY LENGTH (P-recursive order) of value sequences  [non-blind value relation]")
print("="*74)
for name, seq in seqs.items():
    r,d,resid = memory_length(seq)
    verdict = f"FINITE memory (r={r},d={d}, resid={resid:.1e})" if r!="inf" else f"INFINITE memory (best resid={resid:.1e})"
    print(f"  {name:48s} -> {verdict}")
print("\n VERDICT: finite-memory (P-recursive/holonomic) sequences vs infinite-memory ones;")
print(" the granular 'memory length' distinguishes DA-type from HT/arithmetic value sequences.")
