#!/usr/bin/env python3.13
"""
Conjecture E, REDONE with the correct Toda equations (the v1 convention was wrong).

Under measure deformation dμ_t = e^{t x} dμ_0 (so moments satisfy dm_k/dt = m_{k+1}), the monic-OPRL
recurrence coefficients (α_n diagonal, β_n = off-diagonal^2) satisfy the TODA LATTICE.
Derivation of the convention at n=0: α_0=m_1/m_0, dα_0/dt=(m_0 m_2−m_1²)/m_0² = β_1 = β_1−β_0 (β_0=0).
So the correct equations are
      dα_n/dt = β_{n+1} − β_n,      dβ_n/dt = β_n (α_n − α_{n-1})      (α_{-1}=0).
Every OPRL family flows by Toda under e^{tx} — so this is a framework identity; we (1) CONFIRM it on a
well-conditioned (well-spread) node set, free of the v1 clustering noise, then (2) confirm it on the
clustered SECULAR nodes. (3) The nontrivial content for RH is then that the de Bruijn-Newman flow
(weight e^{t u^2}) is the SECOND Toda-hierarchy flow — a separate conjecture, noted not tested here.
"""
import mpmath as mp

mp.mp.dps = 50
K = 8

def alpha_beta(nodes, weights):
    N = len(nodes)
    p_prev = [mp.mpf(0)] * N
    p_cur = [mp.mpf(1)] * N
    def ip(p, q): return sum(weights[i] * p[i] * q[i] for i in range(N))
    norm_cur = ip(p_cur, p_cur); norm_prev = mp.mpf(1)
    al, be = [], []
    for k in range(K):
        a_k = ip([nodes[i] * p_cur[i] for i in range(N)], p_cur) / norm_cur
        b_k = mp.mpf(0) if k == 0 else norm_cur / norm_prev
        al.append(a_k); be.append(b_k)
        p_next = [(nodes[i] - a_k) * p_cur[i] - (b_k * p_prev[i] if k > 0 else 0) for i in range(N)]
        norm_prev = norm_cur; p_prev, p_cur = p_cur, p_next; norm_cur = ip(p_cur, p_cur)
    return al, be

def toda_check(nodes, label):
    eps = mp.mpf('1e-6')
    def cf(t): return alpha_beta(nodes, [mp.e**(t * x) for x in nodes])
    a0, b0 = cf(mp.mpf(0)); ap, bp = cf(eps); am, bm = cf(-eps)
    print(f"\n=== {label} ===")
    print("  n |  dα/dt(num)   β_{n+1}−β_n  | rel  |  dβ/dt(num)   β_n(α_n−α_{n-1}) | rel")
    worst = mp.mpf(0)
    for n in range(1, K - 1):
        dadt = (ap[n] - am[n]) / (2 * eps)
        dbdt = (bp[n] - bm[n]) / (2 * eps)
        rhs_a = b0[n + 1] - b0[n]
        rhs_b = b0[n] * (a0[n] - a0[n - 1])
        ra = abs(dadt - rhs_a) / (abs(rhs_a) + mp.mpf('1e-40'))
        rb = abs(dbdt - rhs_b) / (abs(rhs_b) + mp.mpf('1e-40'))
        worst = max(worst, ra, rb)
        print(f"  {n} | {mp.nstr(dadt,6):>12} {mp.nstr(rhs_a,6):>12} | {mp.nstr(ra,2)} | "
              f"{mp.nstr(dbdt,6):>12} {mp.nstr(rhs_b,6):>12} | {mp.nstr(rb,2)}")
    print(f"  worst rel error = {mp.nstr(worst,3)}  ({'TODA CONFIRMED' if worst < mp.mpf('1e-3') else 'not confirmed'})")
    return worst

def main():
    # (1) well-conditioned spread nodes
    spread = [mp.mpf(x) for x in ['1.5','2.7','3.1','4.6','5.9','7.2','8.8','10.1','11.3','12.9']]
    toda_check(spread, "(1) well-spread nodes (convention validation)")
    # (2) secular nodes u_i = -1/gamma_i^2 (clustered)
    g = [mp.im(mp.zetazero(n)) for n in range(1, 41)]
    u = [-1 / (gi**2) for gi in g]
    sc = 1 / abs(u[0]); u = [sc * ui for ui in u]
    toda_check(u, "(2) secular nodes u_i=-1/γ² (rescaled; clustered)")

if __name__ == "__main__":
    main()
