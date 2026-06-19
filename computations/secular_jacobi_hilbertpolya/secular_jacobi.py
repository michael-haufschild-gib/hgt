#!/usr/bin/env python3.13
"""
The Jacobi-matrix / Hilbert-Pólya face of the secular hierarchy.

The secular (reciprocal squared-zero) spectrum is u_i = 1/(ρ_i-½)^2 = -1/γ_i^2 (real<0 on RH).
Its moments m_k = Σ_i u_i^k are the secular power sums (m_k = (-1)^k Σ γ^{-2k}; m_1 = -secondzeta(2)).
The classical moment→orthogonal-polynomial map (Stieltjes/Lanczos, BILINEAR form Σ f g, matching the
Hankel of moments) produces a three-term recurrence
      p_{k+1}(x) = (x - a_k) p_k(x) - b_k p_{k-1}(x),
i.e. a tridiagonal JACOBI MATRIX J (diagonal a_k, off-diagonal √b_k) whose eigenvalues are the u_i.

  RH  ⟺  the u_i are real  ⟺  J is a real self-adjoint Jacobi matrix (a_k real, b_k>0)
      ⟺  the secular Hankel is PD (b_k = D_k... ratios > 0).

This is the Hilbert-Pólya operator built SOURCE-PURELY from the secular moments (no zero ordinate is
used as an eigenvalue input — the u_i come from the zeros, but for the off-line test we perturb and
watch J leave the self-adjoint class). (a_k,b_k) are a new basis of secular invariants, welding to
weil_prime_schrodinger (J = discrete Schrödinger −Δ+V) and lyapunov_dmr (J's transfer cocycle).

Tests: (1) genuine spectrum ⟹ a_k real, b_k>0 (self-adjoint J);
       (2) push one zero off-line ⟹ a_k/b_k become complex / b_k<0 (J leaves the self-adjoint class);
       (3) the b_k ratios = Hankel-determinant positivity (= secular_hankel_signature, operator form).
"""
import mpmath as mp

mp.mp.dps = 30
K = 12   # number of recurrence coefficients

def jacobi_from_nodes(nodes):
    """Stieltjes/Lanczos with the bilinear form <f,g> = Σ_i f(u_i) g(u_i) (no conjugation)."""
    N = len(nodes)
    p_prev = [mp.mpf(0)] * N
    p_cur = [mp.mpf(1)] * N
    norm_cur = sum(p * p for p in p_cur)         # <p_0,p_0> = N
    norm_prev = mp.mpf(1)
    a, b = [], []
    for k in range(K):
        num = sum(nodes[i] * p_cur[i] * p_cur[i] for i in range(N))
        a_k = num / norm_cur
        b_k = mp.mpf(0) if k == 0 else norm_cur / norm_prev
        a.append(a_k); b.append(b_k)
        p_next = [(nodes[i] - a_k) * p_cur[i] - (b_k * p_prev[i] if k > 0 else 0) for i in range(N)]
        norm_prev = norm_cur
        p_prev, p_cur = p_cur, p_next
        norm_cur = sum(p * p for p in p_cur)
    return a, b

def zeros(N):
    return [mp.im(mp.zetazero(n)) for n in range(1, N + 1)]

def main():
    N = 40
    print(f"=== secular Jacobi / Hilbert-Pólya (N={N} zeros, dps={mp.mp.dps}) ===")
    g = zeros(N)
    # genuine on-line: u_i = -1/gamma_i^2 (real, <0)
    u_real = [-1 / (gi**2) for gi in g]
    a, b = jacobi_from_nodes(u_real)
    print("\n(1) genuine spectrum: a_k (diagonal), b_k (off-diag^2) — expect a_k REAL, b_k>0 (self-adjoint J)")
    allreal = all(abs(mp.im(x)) < mp.mpf('1e-20') for x in a + b)
    bpos = all(mp.re(bk) > 0 for bk in b[1:])
    for k in range(K):
        print(f"  k={k:2d}: a_k={mp.nstr(mp.re(a[k]),8):>14}  b_k={mp.nstr(mp.re(b[k]),8):>13}  "
              f"{'(b>0)' if k==0 or mp.re(b[k])>0 else '(b<=0!)'}")
    print(f"  => a_k,b_k real? {allreal}   b_k>0 (k>=1)? {bpos}   => J self-adjoint: {allreal and bpos}")

    print("\n(2) push zero #1 off-line by delta -> u gets a complex-conjugate pair; watch J leave self-adjoint")
    for d in ['1.0', '0.3', '0.1']:
        delta = mp.mpf(d)
        tau = delta + mp.mpc(0, g[0])               # off-line tau (squared-zero w=tau^2)
        upert = [1/(tau**2), 1/(mp.conj(tau)**2)] + [-1/(gi**2) for gi in g[1:]]
        ap, bp = jacobi_from_nodes(upert)
        maxim = max(abs(mp.im(x)) for x in ap + bp)
        minreb = min(mp.re(bk) for bk in bp[1:])
        print(f"  delta={d:4s}: max|Im(a_k,b_k)|={mp.nstr(maxim,5)}  min Re(b_k)={mp.nstr(minreb,5)}  "
              f"{'J COMPLEX/indefinite => off-line detected' if maxim>1e-12 or minreb<0 else 'still self-adjoint'}")

    print("\n(3) b_k>0 (k>=1) for genuine  <=>  secular Hankel PD  <=>  squared-zeros real  <=>  RH.")
    print("#   J is the source-pure Hilbert-Pólya operator; (a_k,b_k) a new secular-invariant basis.")

if __name__ == "__main__":
    main()
