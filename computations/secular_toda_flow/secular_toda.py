#!/usr/bin/env python3.13
"""
Is the secular Jacobi matrix a Toda-lattice orbit?  (Conjecture E test)

The secular Jacobi matrix J (from secular_jacobi_hilbertpolya) has recurrence coeffs (a_k, b_k).
Classical fact (Flaschka/Moser): deforming the orthogonality measure by e^{t x} evolves (a_k,b_k)
by the TODA LATTICE. In recurrence-coefficient form (b_k = off-diagonal^2):
      da_k/dt = 2 (b_k - b_{k-1}),     db_k/dt = b_k (a_{k+1} - a_k).
If the secular spectrum obeys this, the secular hierarchy sits inside an INTEGRABLE system: the
secular invariants are Toda conserved quantities, and the de Bruijn-Newman flow (weight e^{t u^2})
is the next flow of the Toda hierarchy. RH (Λ≤0) would be "the secular Toda orbit stays in the
self-adjoint stratum (b_k>0) for t≥0," with t=0 the initial datum.

Test: nodes u_i = -1/γ_i^2 (rescaled to O(1)); compute (a_k,b_k)(t) for the e^{t u} measure;
finite-difference d/dt at t=0; compare to the Toda RHS.
"""
import mpmath as mp

mp.mp.dps = 40
K = 9

def jacobi_weighted(nodes, weights):
    N = len(nodes)
    p_prev = [mp.mpf(0)] * N
    p_cur = [mp.mpf(1)] * N
    def ip(p, q): return sum(weights[i] * p[i] * q[i] for i in range(N))
    norm_cur = ip(p_cur, p_cur)
    norm_prev = mp.mpf(1)
    a, b = [], []
    for k in range(K):
        a_k = ip([nodes[i] * p_cur[i] for i in range(N)], p_cur) / norm_cur
        b_k = mp.mpf(0) if k == 0 else norm_cur / norm_prev
        a.append(a_k); b.append(b_k)
        p_next = [(nodes[i] - a_k) * p_cur[i] - (b_k * p_prev[i] if k > 0 else 0) for i in range(N)]
        norm_prev = norm_cur
        p_prev, p_cur = p_cur, p_next
        norm_cur = ip(p_cur, p_cur)
    return a, b

def main():
    N = 40
    g = [mp.im(mp.zetazero(n)) for n in range(1, N + 1)]
    u = [-1 / (gi**2) for gi in g]
    sc = 1 / abs(u[0])
    u = [sc * ui for ui in u]                     # rescale nodes to O(1) (Toda covariant under scaling)
    eps = mp.mpf('1e-5')
    def coeffs(t): return jacobi_weighted(u, [mp.e**(t * ui) for ui in u])
    a0, b0 = coeffs(mp.mpf(0))
    ap, bp = coeffs(eps)
    am, bm = coeffs(-eps)
    print("=== Toda test for the secular Jacobi matrix (measure e^{t u}, rescaled nodes, N=40) ===")
    print("  k |    da_k/dt (num)   2(b_k - b_{k-1}) | rel |    db_k/dt (num)   b_k(a_{k+1}-a_k) | rel")
    for k in range(1, K - 1):
        dadt = (ap[k] - am[k]) / (2 * eps)
        dbdt = (bp[k] - bm[k]) / (2 * eps)
        toda_a = 2 * (b0[k] - b0[k - 1])
        toda_b = b0[k] * (a0[k + 1] - a0[k])
        rela = abs(dadt - toda_a) / (abs(toda_a) + mp.mpf('1e-30'))
        relb = abs(dbdt - toda_b) / (abs(toda_b) + mp.mpf('1e-30'))
        print(f"  {k} | {mp.nstr(dadt,7):>16} {mp.nstr(toda_a,7):>16} | {mp.nstr(rela,3)} | "
              f"{mp.nstr(dbdt,7):>16} {mp.nstr(toda_b,7):>16} | {mp.nstr(relb,3)}")
    print("\n# If rel ~ 0, the secular Jacobi matrix IS a Toda orbit (integrable). Then the secular")
    print("# invariants are Toda conserved quantities and dBN is the e^{t u^2} Toda-hierarchy flow.")

if __name__ == "__main__":
    main()
