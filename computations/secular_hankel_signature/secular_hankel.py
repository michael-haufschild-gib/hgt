#!/usr/bin/env python3.13
"""
Secular Hermite-Hankel experiment for the (B) "RH as byproduct" route.

Object: zeros of xi recentred at 1/2,  tau = rho - 1/2.  Squared-zero w = tau^2.
RH <=> every squared-zero w is real (<=0).
Secular even power sums  s_j = sum_tau tau^{-2j} = sum_alpha u_alpha^j ,  u = tau^{-2}.
Secular Hankel  H_K = [ m_{i+j} ]_{0<=i,j<=K} ,  m_0 = #zeros, m_j = s_j (j>=1).
Hermite: H_K >= 0  for all K  <=>  all u real  <=>  RH.
Jacobi:  #(negative eigenvalues) = #sign changes in (1, D_1, ..., D_K) of leading principal minors
         = #(complex-conjugate pairs of squared-zeros) = #(off-line sigma-quadruples).

We (0) unit-test the Hermite/Jacobi machinery on synthetic point sets,
   (1) cross-check secular constants against mpmath.secondzeta,
   (2) S0: genuine on-line spectrum -> expect PD (0 sign changes, det>0 = simple),
   (3) S1: one zero pushed off-line -> expect negative eigenvalue(s),
   (4) no-margin: shrink the off-line displacement delta -> eigenvalue crossing -> 0,
   (5) rank/simplicity: planted double zero drops the Hankel rank (det -> 0).
"""
import mpmath as mp
from multiprocessing import Pool

mp.mp.dps = 30

# ---------- core linear algebra (mpmath, sign-robust) ----------
def moments(taus, K, scale):
    """m_j = sum over multiset {taus} of (scale*tau^{-2})^j, j=0..2K.  Returns mp reals."""
    us = [scale * tau**(-2) for tau in taus]
    m = []
    for j in range(0, 2*K+1):
        if j == 0:
            m.append(mp.mpf(len(us)))
        else:
            # moments are real by conjugation-symmetry of the multiset; drop ~1e-30 residue
            m.append(mp.re(sum(u**j for u in us)))
    return m

def hankel(m, K):
    return mp.matrix([[m[i+j] for j in range(K+1)] for i in range(K+1)])

def leading_minors(H, K):
    return [mp.mpf(1)] + [mp.det(H[:k, :k]) for k in range(1, K+2)]

def sign_changes(seq):
    """#sign changes in a real sequence (Jacobi: = #negative eigenvalues)."""
    s = [x for x in seq if x != 0]
    return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))

def min_eig(H):
    ev = mp.eigsy(H, eigvals_only=True)
    return min(ev)

# ---------- (0) unit test of the machinery, no zeta ----------
def unit_test():
    print("=== (0) unit test of Hermite/Jacobi on synthetic squared-zeros ===")
    cases = {
        "3 real (PD)":        [mp.mpf(-1), mp.mpf(-2), mp.mpf(-3), mp.mpf(-5)],
        "1 conj pair + reals":[mp.mpf(-1), mp.mpf(-2), mp.mpc(0,1), mp.mpc(0,-1)],
        "2 conj pairs+reals": [mp.mpf(-1), mp.mpc(1,2), mp.mpc(1,-2), mp.mpc(0,3), mp.mpc(0,-3)],
    }
    for name, ws in cases.items():
        # here ws ARE the squared-zeros directly; u = 1/w
        us = [1/w for w in ws]
        K = len(ws) - 1
        m = [mp.mpf(len(us)) if j == 0 else mp.re(sum(u**j for u in us)) for j in range(2*K+1)]
        H = hankel(m, K)
        D = leading_minors(H, K)
        nc = sign_changes(D)
        # count true complex-conjugate pairs
        npairs = sum(1 for w in ws if mp.im(w) > 0)
        print(f"  {name:22s}: sign-changes={nc}  predicted #conj-pairs={npairs}  "
              f"{'OK' if nc==npairs else 'MISMATCH'}")
    print()

# ---------- zeros ----------
def _zero_im(n):
    return mp.im(mp.zetazero(n))

def get_gammas(N):
    with Pool(min(32, N)) as pool:
        return pool.map(_zero_im, range(1, N+1))

def online_taus(gammas):
    """on-line multiset {+- i gamma}."""
    taus = []
    for g in gammas:
        taus.append(mp.mpc(0, g))
        taus.append(mp.mpc(0, -g))
    return taus

def push_offline(gammas, k, delta):
    """replace the on-line pair for zero index k (1-based) by the off-line quadruple
       {+-delta +- i gamma_k}; all other zeros stay on-line."""
    taus = []
    for idx, g in enumerate(gammas, start=1):
        if idx == k:
            for sx in (delta, -delta):
                for sy in (g, -g):
                    taus.append(mp.mpc(sx, sy))
        else:
            taus.append(mp.mpc(0, g))
            taus.append(mp.mpc(0, -g))
    return taus

# ---------- main ----------
def main():
    unit_test()

    N = 120
    K = 12
    print(f"=== computing first N={N} nontrivial zeros (dps={mp.mp.dps}) ===")
    gammas = get_gammas(N)
    g1 = gammas[0]
    scale = g1**2                      # congruence rescale: |u'_1| = 1 (signature-preserving)
    print(f"  gamma_1={mp.nstr(g1,12)}  gamma_N={mp.nstr(gammas[-1],12)}  scale=g1^2={mp.nstr(scale,12)}")

    # (1) cross-check secular constant s_1 = sum_tau tau^{-2} = -2 * sum_{g>0} g^{-2}
    s1_from_zeros = sum(mp.mpc(0, g)**(-2) + mp.mpc(0, -g)**(-2) for g in gammas)
    s1_secondzeta = -2 * mp.secondzeta(2)         # full sum over ALL zeros; truncation differs
    print("\n=== (1) secular constant cross-check (s_1 = sum tau^-2) ===")
    print(f"  s_1 (truncated N={N} zeros)      = {mp.nstr(mp.re(s1_from_zeros),15)}")
    print(f"  -2*secondzeta(2) (all zeros)     = {mp.nstr(mp.re(s1_secondzeta),15)}")
    print(f"  Im(s_1) (should be ~0)           = {mp.nstr(mp.im(s1_from_zeros),6)}")

    # (2) S0 genuine on-line
    print("\n=== (2) S0: genuine on-line spectrum ===")
    m0 = moments(online_taus(gammas), K, scale)
    H0 = hankel(m0, K)
    D0 = leading_minors(H0, K)
    print(f"  leading-minor signs: {''.join('+' if d>0 else '-' if d<0 else '0' for d in D0)}")
    print(f"  sign-changes = {sign_changes(D0)}  (predict 0 => PD => RH-consistent)")
    print(f"  lambda_min(H0) = {mp.nstr(min_eig(H0),6)}  (>0 => PD => RH-consistent; tiny = no-margin)")
    print(f"  Hankel det D_K = {mp.nstr(D0[-1],6)}  (>0; simplicity tested at saturation in block 5)")

    # (3) S1 one zero off-line (lowest zero = strongest signal)
    print("\n=== (3) S1: zero k=1 pushed off-line by delta=0.30 ===")
    m1 = moments(push_offline(gammas, 1, mp.mpf('0.30')), K, scale)
    H1 = hankel(m1, K)
    D1 = leading_minors(H1, K)
    print(f"  leading-minor signs: {''.join('+' if d>0 else '-' if d<0 else '0' for d in D1)}")
    print(f"  sign-changes = {sign_changes(D1)}  (>=1 => indefinite => off-line DETECTED)")
    print(f"  lambda_min(H1) = {mp.nstr(min_eig(H1),6)}  (<0 expected)")

    # (4) no-margin: shrink delta, watch the negative eigenvalue collapse to 0
    print("\n=== (4) no-margin: lambda_min vs off-line displacement delta (zero k=1) ===")
    for d in ['0.50', '0.20', '0.05', '0.01', '0.001']:
        md = moments(push_offline(gammas, 1, mp.mpf(d)), K, scale)
        Hd = hankel(md, K)
        print(f"  delta={d:6s}  sign-changes={sign_changes(leading_minors(Hd,K))}  "
              f"lambda_min={mp.nstr(min_eig(Hd),6)}")

    # (5) rank/simplicity at a SATURATED Hankel: #distinct squared-zeros = rank.
    #     Small spectrum so K+1 ~ #points; a coincident (double) zero drops the rank => det->0.
    print("\n=== (5) rank/simplicity (saturated Hankel, small spectrum) ===")
    nsmall = 6
    gs = gammas[:nsmall]                              # 6 distinct squared-zeros -2*sided
    # use the DISTINCT squared-zero values w_n = -g_n^2 as a positive measure on the reals.
    # rescale u to O(1) (congruence => preserves rank/signature) and lift precision to avoid
    # the catastrophic cancellation that underflowed the raw determinant.
    def small_hankel(wvals):
        with mp.workdps(80):
            sc = abs(wvals[0])
            us = [sc / w for w in wvals]              # |u_1| = 1
            Ks = len(us) - 1
            m = [mp.mpf(len(us)) if j == 0 else mp.re(sum(u**j for u in us)) for j in range(2*Ks+1)]
            return leading_minors(hankel(m, Ks), Ks)[-1], Ks
    w_distinct = [-(g**2) for g in gs]                # 6 distinct -> full rank
    w_double   = w_distinct[:-1] + [w_distinct[-2]]   # collapse w_6 := w_5 -> only 5 distinct
    dD, Ks = small_hankel(w_distinct)
    dC, _  = small_hankel(w_double)
    print(f"  {nsmall} distinct squared-zeros: saturated det D_{Ks} = {mp.nstr(dD,6)}  (!=0 => SIMPLE)")
    print(f"  one coincident (double) zero:  saturated det D_{Ks} = {mp.nstr(dC,6)}  (->0 => rank drop)")
    print(f"  => simplicity of zeros = nonsingularity of the secular Hankel (the transcendence byproduct).")

if __name__ == "__main__":
    main()
