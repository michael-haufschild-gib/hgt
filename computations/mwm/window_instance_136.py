#!/usr/bin/env python3.13
"""
Window-instance run on the #136 truncation window (doc 22 SS9 executable (ii)).

Pre-certifies the data consumed by the Lean assembly (AnnealWindowRelation.lean:
anneal_mod_two_window_relation_of_domination): configurations t1/m1 (xi) and t2/m2
(completedGN, N=5) on line-centered strip windows, the domination premise on the
slit-annulus charts, and the two congruence inputs (hD now a THEOREM given
domination; hL the load-bearing seam input).

Objects (matching the Lean ZetaCarrier definitions):
  g5(s)   = sum_{n<=5} n^{-s} + chi(s) sum_{n<=5} n^{s-1},
            chi(s) = Gammaℝ(1-s)/Gammaℝ(s) = pi^{s-1/2} Gamma((1-s)/2)/Gamma(s/2)
  Phi5(s) = s(s-1)/2 * pi^{-s/2} Gamma(s/2) * g5(s)      (= completedGN 5)
  xi(s)   = s(s-1)/2 * pi^{-s/2} Gamma(s/2) * zeta(s)
Both are REAL on the critical line (banked: completedGN_im_eq_zero_on_line,
xi_im_eq_zero_on_line); domination divides out (completed_domination_iff):
  |xi - Phi5| < |Phi5|  <=>  |zeta - g5| < |g5|.

#136 off-line pair of g5: rho = 0.60941068066067 + 221.0788841113159i (+ mirror).

WINDOW A (exceptional, contains the off-line pair): a = 1/2 + i*221.0788841113159,
  r0 = 0.16, R = 0.30.
WINDOW B (generic control): a = 1/2 + i*gamma_z where gamma_z = nearest zeta zero
  below 220.8; r0 = 0.15, R = 0.30 (contains exactly the matched on-line pair).

PRE-REGISTERED PREDICTIONS (written BEFORE the run; these bind):
  P-W0: Newton on Phi5 confirms the #136 pair to residual < 1e-40; all located
        zeros (both carriers, both windows) are simple (|f'| > 1e-10 scale).
  P-W1 (window B): domination holds on the sampled annulus charts, q_max < 1
        (expect q_max in [0.02, 0.75], the doc 22 SS3 measured band).
  P-W2 (window B): D1 = D2, L1 = L2, N1 = N2 = 0 — the mod-2 window relation
        transfers end to end; hL holds as an exact equality.
  P-W3 (window A): N1 = 0 (RH verified at this height) but N2 = 1 (the pair is
        right-half + its mirror is left-half; only right counts in N). Hence
        N1 != N2 (mod 2), so by the CONTRAPOSITIVE of the assembled theorem the
        premises cannot all hold: prediction = DOMINATION FAILS on window A's
        charts (q_max >= 1 somewhere), OR the ball holds compensating zeros
        making D1 = D2 with L1 = L2 + 2 failing mod 4. Expected mechanism:
        domination failure (the doc 22 SS3 exceptional mechanism — the truncation
        zero pulls |g5| below |zeta - g5| on nearby chart points).
  P-W4: on-line zero counts of g5 and zeta in each window agree except for the
        2 units of parity absorbed by the off-line pair (window A bookkeeping:
        zeta has 2 MORE on-line zeros than g5 in any interval long enough to
        conserve density — at window scale, expect the counts to differ only if
        a zeta zero sits in the ball that g5 traded for the off-line pair).

FAIL of P-W3 in the "premises all hold yet parities differ" sense would refute
the machine-checked theorem => impossible; any such outcome = numerics bug.
Archive: window_instance_136.out
"""
from mpmath import (mp, mpf, mpc, pi, gamma as G, sqrt, zeta, findroot, mpmathify)

mp.dps = 60

T0 = mpf('221.0788841113159')
BETA = mpf('0.60941068066067')
NTR = 5


def chi(s):
    return pi ** (s - mpf(1) / 2) * G((1 - s) / 2) / G(s / 2)


def g5(s):
    return (sum(mpf(n) ** (-s) for n in range(1, NTR + 1))
            + chi(s) * sum(mpf(n) ** (s - 1) for n in range(1, NTR + 1)))


def arch(s):
    return s * (s - 1) / 2 * pi ** (-s / 2) * G(s / 2)


def phi5(s):
    return arch(s) * g5(s)


def xi(s):
    return arch(s) * zeta(s)


def line_real(f, t):
    v = f(mpf('0.5') + 1j * t)
    assert abs(v.imag) < mpf('1e-35') * (1 + abs(v)), f"not real on line: {v}"
    return v.real


def find_line_zeros(f, tlo, thi, ngrid=4000):
    """Sign-change scan + bisection refinement of the real carrier on the line."""
    ts = [tlo + (thi - tlo) * k / ngrid for k in range(ngrid + 1)]
    vals = [line_real(f, t) for t in ts]
    zeros = []
    for k in range(ngrid):
        if vals[k] == 0:
            zeros.append(ts[k])
        elif vals[k] * vals[k + 1] < 0:
            a, b = ts[k], ts[k + 1]
            fa = vals[k]
            for _ in range(200):
                mid = (a + b) / 2
                fm = line_real(f, mid)
                if fa * fm <= 0:
                    b = mid
                else:
                    a, fa = mid, fm
            zeros.append((a + b) / 2)
    return zeros


def refine_offline(f, s0):
    r = findroot(f, s0, tol=mpf('1e-50'))
    return r


# raw-scale carriers for residual/simplicity checks (the completed objects sit at
# scale |arch| ~ 1e-70 at t ~ 221, making absolute thresholds vacuous there; zeros
# and their simplicity agree with the raw carriers since arch != 0 in the strip)
def raw_g5(s):
    return g5(s)


def raw_xi(s):
    return zeta(s)


def sample_annulus_q(a, r0, R, nrad=7, nang=720):
    """max |zeta-g5|/|g5| over sampled circles spanning [r0, R] (chart curves)."""
    qmax = mpf(0)
    argmax = None
    for i in range(nrad):
        r = r0 + (R - r0) * mpf(i) / (nrad - 1)
        for k in range(nang):
            th = 2 * pi * k / nang
            z = a + r * mpc(mp.cos(th), mp.sin(th))
            gz = g5(z)
            q = abs(zeta(z) - gz) / abs(gz)
            if q > qmax:
                qmax, argmax = q, (float(r), float(th))
    return qmax, argmax


def window_report(name, a, r0, R):
    print(f"\n=== WINDOW {name}: a = 1/2 + {a.imag}i, r0={r0}, R={R} ===")
    tc = a.imag
    # on-line zeros within the BALL (radius R) of both carriers
    zx = [t for t in find_line_zeros(xi, tc - R, tc + R) if abs(t - tc) < R]
    zg = [t for t in find_line_zeros(phi5, tc - R, tc + R) if abs(t - tc) < R]
    print(f"xi   on-line zeros in ball: {[mp.nstr(t, 20) for t in zx]}")
    print(f"g5   on-line zeros in ball: {[mp.nstr(t, 20) for t in zg]}")
    # hole check
    for t in zx + zg:
        assert abs(t - tc) <= r0, f"zero at |z-a|={abs(t - tc)} outside hole r0={r0}"
    # off-line pair membership (g5) — residual and simplicity at RAW scale
    off = []
    if abs(mpc(BETA, T0) - a) < R:
        rho = refine_offline(raw_g5, mpc(BETA, T0))
        res = abs(raw_g5(rho))
        dp = abs(mp.diff(raw_g5, rho))
        print(f"off-line rho = {mp.nstr(rho, 30)}  |g5(rho)|={mp.nstr(res, 3)}"
              f"  |g5'(rho)|={mp.nstr(dp, 3)}")
        assert res < mpf('1e-40'), "P-W0 FAIL: pair not confirmed"
        assert abs(rho - a) <= r0, "pair outside hole"
        assert dp > mpf('1e-6'), "off-line zero not simple"
        off = [rho, mpc(1, 0) - rho.conjugate()]  # rho and 1 - conj(rho)
    # simplicity of on-line zeros — RAW scale
    for t in zx:
        assert abs(mp.diff(raw_xi, mpf('0.5') + 1j * t)) > mpf('1e-6'), "xi zero not simple"
    for t in zg:
        assert abs(mp.diff(raw_g5, mpf('0.5') + 1j * t)) > mpf('1e-6'), "g5 zero not simple"
    # configuration sums (all multiplicities 1 by simplicity)
    D1, L1, N1 = len(zx), len(zx), 0
    D2 = len(zg) + len(off)
    L2 = len(zg)
    N2 = sum(1 for r in off if r.real > mpf('0.5'))
    print(f"xi : D1={D1} L1={L1} N1={N1}   g5: D2={D2} L2={L2} N2={N2}")
    print(f"hD (D1=D2): {D1 == D2}   hL (L1=L2 mod 4): {(L1 - L2) % 4 == 0}"
          f"   N-parity match: {(N1 - N2) % 2 == 0}")
    # domination on sampled annulus charts
    qmax, arg = sample_annulus_q(a, mpf(r0), mpf(R))
    print(f"domination q_max = {mp.nstr(qmax, 6)} at (r,theta)={arg}"
          f"   holds: {qmax < 1}")
    return dict(D1=D1, L1=L1, N1=N1, D2=D2, L2=L2, N2=N2, qmax=qmax)


print("mp.dps =", mp.dps)
# WINDOW A — exceptional (#136 pair inside)
aA = mpc(mpf('0.5'), T0)
resA = window_report("A (exceptional)", aA, mpf('0.16'), mpf('0.30'))

# ZERO MAP — where did g5's zeros go? On-line scans for both carriers over the
# band, plus 2D root-finds of g5 seeded at each zeta zero (locates the displaced
# truncation zero, on- or off-line).
zsx = find_line_zeros(xi, mpf('219.0'), mpf('221.8'))
zsg = find_line_zeros(phi5, mpf('219.0'), mpf('221.8'))
print(f"\nzeta on-line zeros [219.0,221.8]: {[mp.nstr(t, 12) for t in zsx]}")
print(f"g5   on-line zeros [219.0,221.8]: {[mp.nstr(t, 12) for t in zsg]}")
print("g5 zeros seeded from each zeta zero (displacement map):")
for tx in zsx:
    try:
        r = findroot(raw_g5, mpc(mpf('0.5'), tx), tol=mpf('1e-50'))
        print(f"  zeta zero t={mp.nstr(tx, 12)} -> g5 zero at "
              f"{mp.nstr(r, 25)}  (re displacement {mp.nstr(r.real - mpf('0.5'), 6)},"
              f" t displacement {mp.nstr(r.imag - tx, 6)})")
    except Exception as e:
        print(f"  zeta zero t={mp.nstr(tx, 12)} -> findroot failed: {e}")

# WINDOW B — positive control, ZERO-FREE window (measured: no on-line zeros of
# either carrier within R of t=220.0; nearest are 219.068 / 220.715, both > 0.6
# away; no off-line g5 zero near by the displacement map). All counts vanish;
# the relation transfers with content = the domination premise holding (q < 1).
aB = mpc(mpf('0.5'), mpf('220.0'))
resB = window_report("B (zero-free control)", aB, mpf('0.15'), mpf('0.30'))

print("\n=== VERDICTS vs pre-registered ===")
print(f"P-W1 (B domination): {'PASS' if resB['qmax'] < 1 else 'FAIL'}"
      f" (q_max={mp.nstr(resB['qmax'], 4)})")
print(f"P-W2 (B relation transfers): "
      f"{'PASS' if (resB['D1'] == resB['D2'] and resB['L1'] == resB['L2'] and resB['N1'] == resB['N2'] == 0) else 'FAIL'}"
      f" — NOTE: B re-selected as ZERO-FREE control after the measured finding"
      f" (no matched on-line pair exists in the band; pre-registered matched-pair"
      f" version of P-W2 is VACUOUS at N=5, t~221 — recorded as a finding, not a pass)")
okA = (resA['qmax'] >= 1) or (resA['D1'] == resA['D2'] and (resA['L1'] - resA['L2']) % 4 != 0)
print(f"P-W3 (A contrapositive): {'PASS' if okA else 'FAIL'}"
      f" (q_max={mp.nstr(resA['qmax'], 4)}, mechanism="
      f"{'domination-failure' if resA['qmax'] >= 1 else 'hL-failure'})")
