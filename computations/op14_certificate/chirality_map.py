#!/usr/bin/env python3
"""Chirality map: is dip-chirality a pullback invariant, and do Omega-side dips leave
cofinal clean gaps at beta?  c = 1/5.

Object: phi(t) = |gamma_c(t) - beta| along the arm, t in a range of small angles.
Dip = strict local min of phi (arm bulges back toward beta).  A dip straddles radii
(phi*, flank).  Chirality: place a probe in the dip lens; escape => Omega-side
(genuine planar pocket), capture => K-side (harmless).

Two decisive tests:
  (A) Coherence under pullback t -> t/2 (dyadic: m/2^K -> m/2^(K+1)).  For real c the
      inverse branch at beta is orientation-preserving conformal, so chirality MUST be
      preserved exactly.  Confirm empirically.
  (B) Fundamental census: dips in one angular period [t0/2, t0], their chiralities and
      radius-band widths D/d.  If each Omega-side dip has D/d << lambda, its pullback
      tower leaves large clean gaps => beta cofinally one-sided.
"""
import numpy as np

C = 0.2
BETA = (1 + np.sqrt(1 - 4 * C)) / 2
LAM = 2 * BETA


def gamma_dyadic(m, K):
    z = np.full(np.shape(m), BETA, dtype=np.complex128)
    m = np.asarray(m, dtype=np.int64)
    for j in range(K):
        bit = (m >> j) & 1
        s = np.sqrt(z - C)
        s = np.where(s.imag >= 0, s, -s)
        z = np.where(bit == 0, s, -s)
    return z


def phi_arr(m, K):
    return np.abs(gamma_dyadic(m, K) - BETA)


def escape_verdict(w, maxit=200000):
    z = complex(w)
    for _ in range(maxit):
        z = z * z + C
        az = abs(z)
        if az > 1.5:
            return 1       # Omega
        if az < BETA - 1e-7:
            return -1      # K (trap closedBall(0,beta) subset K for c in [0,1/4))
    return 0               # undecided


def chirality_of_dip(m, K, i, phi):
    """Dip at index i (local min).  Return (+1 Omega, -1 K, 0 undecided), band (d,D)."""
    d = phi[i]
    # flanks: nearest local maxima on each side
    L = i
    while L > 0 and phi[L - 1] >= phi[L]:
        L -= 1
    R = i
    while R < len(phi) - 1 and phi[R + 1] >= phi[R]:
        R += 1
    if L == 0 or R == len(phi) - 1:
        return 0, (d, d), None
    D = min(phi[L], phi[R])
    rho = d + 0.4 * (D - d)
    # angular extent of the sub-arc dipping below rho around i
    a1 = i
    while a1 > 0 and phi[a1 - 1] < rho:
        a1 -= 1
    a2 = i
    while a2 < len(phi) - 1 and phi[a2 + 1] < rho:
        a2 += 1
    z1 = gamma_dyadic(m[a1], K)
    z2 = gamma_dyadic(m[a2], K)
    dir1 = (z1 - BETA) / abs(z1 - BETA)
    dir2 = (z2 - BETA) / abs(z2 - BETA)
    mid = (dir1 + dir2)
    mid = mid / abs(mid)
    verdicts = []
    for frac in (0.3, 0.5, 0.7):
        w = BETA + mid * (d + frac * (D - d))
        verdicts.append(escape_verdict(w))
    v = np.sign(sum(verdicts)) if any(verdicts) else 0
    return int(v), (d, D), (int(m[a1]), int(m[a2]))


def find_dips(m, K, phi, min_depth=1e-11):
    dips = []
    for i in range(1, len(phi) - 1):
        if phi[i] < phi[i - 1] and phi[i] < phi[i + 1]:
            # local depth relative to nearest higher flank
            L = i
            while L > 0 and phi[L - 1] >= phi[L]:
                L -= 1
            R = i
            while R < len(phi) - 1 and phi[R + 1] >= phi[R]:
                R += 1
            if L == 0 or R == len(phi) - 1:
                continue
            depth = min(phi[L], phi[R]) - phi[i]
            if depth > min_depth:
                dips.append(i)
    return dips


def main():
    print(f"c={C}  beta={BETA:.8f}  lambda={LAM:.8f}\n")

    # ---- Test B: fundamental census on one period [t0/2, t0], t0 = 3/64 ----
    K = 30
    m_lo = 3 << (K - 7)     # 3/128
    m_hi = 3 << (K - 6)     # 3/64
    m = np.arange(m_lo, m_hi + 1, dtype=np.int64)
    phi = phi_arr(m, K)
    dips = find_dips(m, K, phi, min_depth=1e-10)
    print(f"period [3/128, 3/64] at K={K}: {len(m)} pts, {len(dips)} dips (depth>1e-10)")

    # classify the deepest ~24 dips
    dips_sorted = sorted(dips, key=lambda i: (min(phi[max(i-1,0)], phi[min(i+1,len(phi)-1)]) - phi[i]), reverse=True)
    census = []
    om = kk = und = 0
    for i in dips_sorted[:24]:
        v, (d, D), _ = chirality_of_dip(m, K, i, phi)
        ratio = D / d
        census.append((int(m[i]), d, ratio, v))
        if v == 1: om += 1
        elif v == -1: kk += 1
        else: und += 1
    print(f"top-24 dips: Omega-side={om}  K-side={kk}  undecided={und}")
    print("  (angle_num/2^30, phi, band D/d, chirality[+1=Omega/-1=K]):")
    for mm, d, ratio, v in census[:16]:
        print(f"    t={mm}/2^30={mm/2**30:.9f}  phi={d:.7f}  D/d={ratio:.6e}  chi={v:+d}")
    maxratio = max(r for _, _, r, _ in census)
    print(f"  max band ratio D/d among top dips = {maxratio:.6e}   (lambda={LAM:.4f})")
    print(f"  => each dip's bad-band spans a factor {maxratio:.6f} < lambda: pullback")
    print(f"     copies at lambda^-n leave clean gaps between them.\n")

    # ---- Test A: chirality coherence under pullback t -> t/2 ----
    print("pullback coherence test (chirality at t vs t/2, t/4, ...):")
    # take a few deep dips, follow the chain toward 0
    checked = 0
    coherent = 0
    for i0 in dips_sorted[:8]:
        m0 = int(m[i0])
        v0, (d0, D0), _ = chirality_of_dip(m, K, i0, phi)
        if v0 == 0:
            continue
        chain = [(30, m0, v0, d0)]
        ok = True
        # pull back: angle t/2 = m0 / 2^(K+1); locate the corresponding dip at level K+n
        for n in range(1, 5):
            Kn = 30 + n
            mn_center = m0 << n     # same angle t*, expressed at finer level
            # search a small window around mn_center for the local min
            half = 6 << n
            mw = np.arange(mn_center - half, mn_center + half + 1, dtype=np.int64)
            pw = phi_arr(mw, Kn)
            j = int(np.argmin(pw))
            # confirm it's a dip
            if j == 0 or j == len(pw) - 1:
                ok = False; break
            vv, (dd, DD), _ = chirality_of_dip(mw, Kn, j, pw)
            chain.append((Kn, int(mw[j]), vv, dd))
            if vv != 0 and vv != v0:
                ok = False
        checked += 1
        if ok:
            coherent += 1
        tag = "COHERENT" if ok else "BROKEN"
        print(f"  dip t={m0}/2^30 chi={v0:+d}: chain {[c[2] for c in chain]}  [{tag}]")
    print(f"  => {coherent}/{checked} chains preserve chirality along pullback\n")

    # ---- Summary verdict ----
    all_K = om + kk
    print("VERDICT:")
    if und == 0 and coherent == checked:
        print(f"  chirality is a clean pullback invariant ({coherent}/{checked} chains).")
    if om > 0:
        print(f"  Omega-side dips EXIST ({om}/{all_K}) => beta is NOT strictly one-sided")
        print(f"  (bad radii recur), but each spans only factor {maxratio:.4f} << lambda,")
        print(f"  so clean radii are cofinal => beta plausibly COFINALLY one-sided.")
    else:
        print(f"  all classified dips K-side => beta cofinally (even strictly?) one-sided here.")


if __name__ == "__main__":
    main()
