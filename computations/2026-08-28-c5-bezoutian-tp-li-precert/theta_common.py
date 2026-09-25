"""Common exact implementations of the Lean corpus objects.

Transcribed literally from:
  formal/GaloisForLFunctions/RHTower/ThetaCuspFinitePrimeSource.lean
    thetaCuspSeed t          = 2*pi*(2*pi*t^4 - 3*t^2) * exp(-pi*t^2)
    thetaCuspSourceTerm x n  = exp(x/2) * thetaCuspSeed(n * exp(x))
    thetaCuspFullSource x    = sum_{n>=1} thetaCuspSourceTerm x n   (n=0 term is 0)
  ThetaCuspKernelLogConcavity.lean
    thetaCuspLogSource x     = log(thetaCuspFullSource x)
  ThetaCuspGlobalReflectedRiccati.lean
    q  (u,t) = 2 L(u) - L(u+t) - L(u-t)                 (reflected log action)
    q1 (u,t) = L'(u-t) - L'(u+t)                        (JetOne  = d/dt q)
    q2 (u,t) = -L''(u+t) - L''(u-t)                     (JetTwo  = d2/dt2 q)
  HedenmalmCenterMixedCorrelationAngle.lean
    P  (u,t) = Phi(u+t) * Phi(u-t)
  ThetaCuspCenterMixedPtolemyTransport.lean
    A  (u,t) = P(u,0) - P(u,t)
  ThetaCuspReflectedSourceOddStationary.lean
    D  (u,t) = P(u,t) * q1(u,t)
  ThetaCuspReflectedSourceOddStationaryCurvature.lean
    J  (u,t) = P(u,t) * (q2 - q1^2)
  ThetaCuspReflectedSourceFifthRootCurvature.lean
    C5 (u,t) = 24 A^2 - 9 t A D + t^2 (5 A J - 4 D^2)
    ratio    = (2A - tD) / (t^2 (12A - tD))
    y        = (2A - tD) / A
    action form: 24 r^2 - 9 t r q1 + t^2 (5 r (q2 - q1^2) - 4 q1^2),  r = exp(q)-1
  RiemannTower.lean
    xi s     = s(s-1)/2 * Lambda0(s) + 1/2  ==  (1/2) s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)
  XiShiftLoewnerCriticalGenerator.lean
    xiCent W = xi(1/2 + W)
  XiBezoutianPointedIncidence.lean
    N(w,y)   = xiCent'(w) xiCent(y) + xiCent(w) xiCent'(y)
    B(w,y)   = N(w,y) / (w + y)      (dslope across the antidiagonal)
"""

import mpmath as mp


# ---------------------------------------------------------------- theta side

def phi_derivs(x, order=2, eps_extra=12):
    """Return [Phi(x), Phi'(x), ..., Phi^(order)(x)].

    Phi is even (Lean theorem `thetaCuspFullSource_neg`), and the literal
    series suffers catastrophic cancellation for x << 0, so we evaluate the
    series at |x| and restore derivatives by parity:
      Phi even, Phi' odd, Phi'' even, Phi''' odd.

    term(n) = K4 e^{a4 x - c} + K2 e^{a2 x - c},  c = pi n^2 e^{2x}, c' = 2c
      K4 = 4 pi^2 n^4, a4 = 9/2 ;  K2 = -6 pi n^2, a2 = 5/2
    d/dx e^{a x - c} = (a - 2c) e^{a x - c}
      f0 = e, f1 = g e, f2 = (g^2 - 4c) e, f3 = (g^3 - 12 c g - 8 c) e,  g = a - 2c
    """
    x = mp.mpf(x)
    sgn = 1 if x >= 0 else -1
    x = abs(x)
    pi = mp.pi
    e2x = mp.e ** (2 * x)
    tol = mp.mpf(10) ** (-(mp.mp.dps + eps_extra))
    out = [mp.mpf(0) for _ in range(order + 1)]
    scale = mp.mpf(0)  # running max magnitude for relative cutoff
    n = 1
    while True:
        nn = mp.mpf(n)
        c = pi * nn ** 2 * e2x
        contrib_mag = mp.mpf(0)
        for (K, a) in ((4 * pi ** 2 * nn ** 4, mp.mpf(9) / 2),
                       (-6 * pi * nn ** 2, mp.mpf(5) / 2)):
            e = K * mp.e ** (a * x - c)
            g = a - 2 * c
            vals = [e]
            if order >= 1:
                vals.append(g * e)
            if order >= 2:
                vals.append((g ** 2 - 4 * c) * e)
            if order >= 3:
                vals.append((g ** 3 - 12 * c * g - 8 * c) * e)
            for k in range(order + 1):
                out[k] += vals[k]
                m = abs(vals[k])
                if m > contrib_mag:
                    contrib_mag = m
        if contrib_mag > scale:
            scale = contrib_mag
        # stop when this term is negligible relative to the largest seen
        if n > 3 and contrib_mag < tol * (scale + tol):
            break
        n += 1
        if n > 10 ** 7:
            raise RuntimeError("phi_derivs: no convergence at x=%s" % x)
    if sgn < 0:
        for k in range(order + 1):
            if k % 2 == 1:
                out[k] = -out[k]
    return out


def c5_point(u, t):
    """All C5-related observables at one fibre point (u, t), t > 0.

    Returns dict with C5/P^2 (action form recomputed two ways), C5/A^2
    (= barrier defect), y, r, t*q1, t^2*q2, plus consistency deltas.
    """
    u = mp.mpf(u)
    t = mp.mpf(t)
    P0m = phi_derivs(u, order=0)
    ppl = phi_derivs(u + t, order=2)
    pmi = phi_derivs(u - t, order=2)
    Phi_u = P0m[0]
    Pp, Pp1, Pp2 = ppl
    Pm, Pm1, Pm2 = pmi
    P0 = Phi_u ** 2
    P = Pp * Pm
    # log-derivatives of Phi at u+t, u-t
    lp1 = Pp1 / Pp
    lp2 = Pp2 / Pp - lp1 ** 2      # L'' (u+t)
    lm1 = Pm1 / Pm
    lm2 = Pm2 / Pm - lm1 ** 2      # L'' (u-t)
    q1 = lm1 - lp1
    q2 = -lp2 - lm2
    q = 2 * mp.log(Phi_u) - mp.log(Pp) - mp.log(Pm)
    r = mp.expm1(q)
    A = P0 - P
    D = P * q1
    J = P * (q2 - q1 ** 2)
    C5 = 24 * A ** 2 - 9 * t * A * D + t ** 2 * (5 * A * J - 4 * D ** 2)
    action = 24 * r ** 2 - 9 * t * r * q1 + t ** 2 * (5 * r * (q2 - q1 ** 2) - 4 * q1 ** 2)
    # barrier defect  B = y(10+y) - 5 t y'   with  y = (2A - tD)/A,
    # y' = -[(D + tJ)A - tD^2]/A^2   (A' = D, D' = J)
    y = (2 * A - t * D) / A
    yprime = -((D + t * J) * A - t * D ** 2) / A ** 2
    B = y * (10 + y) - 5 * t * yprime
    chk_action = C5 / P ** 2 - action          # should be ~0
    chk_barrier = C5 / A ** 2 - B              # should be ~0
    return {
        "u": u, "t": t,
        "c5_over_P2": C5 / P ** 2,
        "c5_over_A2": C5 / A ** 2,
        "y": y, "r": r, "tq1": t * q1, "t2q2": t ** 2 * q2,
        "chk_action": chk_action, "chk_barrier": chk_barrier,
    }


# ------------------------------------------------------------------- xi side

def xi(s):
    """xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s); entire, xi(0)=1/2."""
    s = mp.mpc(s)
    if abs(s) < mp.mpf(10) ** (-30):
        # removable point; not used for our node ranges but keep safe
        return mp.mpf(1) / 2
    return mp.mpf('0.5') * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def xic_and_deriv(w, h=None):
    """xiCent(w) = xi(1/2 + w) and derivative via central differences.

    Uses a 4-point stencil with step ~ 10^{-dps/3} for ~2dps/3 correct digits.
    """
    w = mp.mpc(w)
    if h is None:
        h = mp.mpf(10) ** (-(mp.mp.dps // 3))
    s = mp.mpf(1) / 2 + w
    f = xi(s)
    f1 = xi(s + h)
    f_1 = xi(s - h)
    f2 = xi(s + 2 * h)
    f_2 = xi(s - 2 * h)
    d = (8 * (f1 - f_1) - (f2 - f_2)) / (12 * h)
    return f, d


def bezoutian_matrix(nodes, prec_cache=None):
    """M[j][k] = B(w_j, conj(w_k)),  B(w,y) = (xic'(w) xic(y) + xic(w) xic'(y))/(w+y).

    nodes: list of mpc with Re > 1/2. Returns mp.matrix (Hermitian).
    """
    vals = []
    for wj in nodes:
        vals.append(xic_and_deriv(wj))
    n = len(nodes)
    M = mp.matrix(n, n)
    for j in range(n):
        fj, dj = vals[j]
        for k in range(n):
            fk, dk = vals[k]
            # xic has real Taylor coefficients: xic(conj z) = conj(xic(z))
            fkc = mp.conj(fk)
            dkc = mp.conj(dk)
            w = nodes[j]
            yc = mp.conj(nodes[k])
            M[j, k] = (dj * fkc + fj * dkc) / (w + yc)
    return M


def hermitian_min_max_eig(M):
    """Eigenvalues of a complex Hermitian mp.matrix (mpmath eighe)."""
    E = mp.eighe(M, eigvals_only=True)
    ev = sorted([mp.re(x) for x in E])
    return ev[0], ev[-1], ev


def log10_or_none(x):
    try:
        if x == 0:
            return None
        return float(mp.log10(abs(x)))
    except Exception:
        return None
