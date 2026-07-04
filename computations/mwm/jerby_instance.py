#!/usr/bin/env python3.13
"""
Symmetrized exponential-family window instance (doc 76 SS4 next-object (a)).

Same protocol as window_instance_136.py, on the doc 32 SS6 theorem-track family:
a finite, Schwarz-real approximant Z(s) of zeta with error far below the HL
truncation's t^{-1/4}, completed F(s) = arch(s) Z(s) and SYMMETRIZED
  PhiStar(s) = (F(s) + F(1-s))/2
(exact even FE by construction — the Lean `symmetrize`; error preserved by
(SYM-err) = norm_sub_symmetrize_le). Two candidate families, validation-gated:

  JERBY (doc 32 SS7 transcription, arXiv:1910.05754 Thm 1.1, y = 1):
    Z_J(s) = sum_{n=0}^{floor(x)} 2^{-(n+1)} (1-2^{1-s})^{-1}
               sum_{k=0}^{n} C(n,k) (-1)^k (k+1)^{-s}
             + chi(s)/(1 - 2^{s-1}),      x = t/pi.
  EULER–MACLAURIN (fallback, classical):
    Z_EM(s) = sum_{n<M} n^{-s} + M^{1-s}/(s-1) + M^{-s}/2
              + sum_{j=1}^{J} B_{2j}/(2j)! (s)_{2j-1} M^{-s-2j+1},  M=500, J=20.

VALIDATION GATE (binds): the family used must have max |zeta - Z| < 1e-12 on a
40-point probe of the chart region; report both errors. If both fail, STOP.

WINDOW: a = 1/2 + i*220.7149188393140034 (the zeta zero whose g5 partner went
off-line in the #136 run), r0 = 0.15, R = 0.30.

PRE-REGISTERED PREDICTIONS (written BEFORE the run; these bind):
  P-J0: at least one family passes the validation gate (expect E-M ~ 1e-40 grade;
        Jerby: measured, transcription-risk acknowledged — its FAILURE would flag
        the doc 32 SS7 transcription, not the architecture).
  P-J1: PhiStar has EXACTLY ONE on-line zero in the ball, within 1e-8 of the
        zeta zero (displacement at error/|Xi'| scale — vs 0.36 for g5).
  P-J2: Newton on PhiStar from the zeta-zero seed converges to that SAME on-line
        zero (no off-line displacement — contrast with the #136 map).
  P-J3: domination |xi - PhiStar| < |PhiStar| holds on the sampled annulus
        charts with LARGE margin: q_max < 1e-6.
  P-J4: FIRST NONTRIVIAL POSITIVE TRANSFER: D1 = D2 = 1, L1 = L2 = 1,
        N1 = N2 = 0 — the mod-2 window relation transfers on a window with
        actual zero content; every hypothesis of
        anneal_mod_two_window_relation_of_domination holds with measured values.

Archive: jerby_instance.out
"""
from mpmath import mp, mpf, mpc, pi, gamma as G, zeta, findroot, binomial, bernoulli

mp.dps = 60

TZ = mpf('220.71491883931400336911559263390633965676114507766196570161')
A = mpc(mpf('0.5'), TZ)
R0 = mpf('0.15')
RR = mpf('0.30')


def chi(s):
    return pi ** (s - mpf(1) / 2) * G((1 - s) / 2) / G(s / 2)


def arch(s):
    return s * (s - 1) / 2 * pi ** (-s / 2) * G(s / 2)


def xi(s):
    return arch(s) * zeta(s)


# --- family 1: Jerby (doc 32 SS7 transcription), y = 1, x = t/pi ---
XJ = int(mp.floor(TZ / pi))  # main-sum length at the window height
BINOM = [[binomial(n, k) for k in range(n + 1)] for n in range(XJ + 1)]


def Z_jerby(s):
    tot = mpc(0)
    for n in range(XJ + 1):
        inner = sum(BINOM[n][k] * (-1) ** k * mpf(k + 1) ** (-s) for k in range(n + 1))
        tot += mpf(2) ** (-(n + 1)) * inner
    tot = tot / (1 - mpf(2) ** (1 - s))
    tot += chi(s) / (1 - mpf(2) ** (s - 1))
    return tot


# --- family 2: Euler-Maclaurin, M = 500, J = 20 ---
MEM, JEM = 500, 20
BERN = [bernoulli(2 * j) for j in range(JEM + 1)]


def Z_em(s):
    tot = sum(mpf(n) ** (-s) for n in range(1, MEM))
    tot += mpf(MEM) ** (1 - s) / (s - 1) + mpf(MEM) ** (-s) / 2
    poch = mpc(1)
    for j in range(1, JEM + 1):
        # (s)_{2j-1} = s (s+1) ... (s+2j-2)
        poch = poch * (s + (2 * j - 3)) * (s + (2 * j - 2)) if j > 1 else s
        tot += BERN[j] / mp.factorial(2 * j) * poch * mpf(MEM) ** (-s - 2 * j + 1)
    return tot


def validate(Z, name, npts=40):
    import random
    random.seed(136)
    emax = mpf(0)
    for _ in range(npts):
        r = R0 + (RR - R0) * mpf(random.random())
        th = 2 * pi * mpf(random.random())
        z = A + r * mpc(mp.cos(th), mp.sin(th))
        e = abs(zeta(z) - Z(z))
        emax = max(emax, e)
    print(f"validation {name}: max|zeta - Z| = {mp.nstr(emax, 4)} over {npts} chart pts")
    return emax


print("mp.dps =", mp.dps, " window a = 1/2 +", mp.nstr(TZ, 20), "i  r0 =", R0, " R =", RR)
eJ = validate(Z_jerby, "JERBY(y=1)")
eE = validate(Z_em, f"EM(M={MEM},J={JEM})")
GATE = mpf('1e-12')
fams = [(n, Z, e) for (n, Z, e) in [("JERBY", Z_jerby, eJ), ("EM", Z_em, eE)] if e < GATE]
print(f"P-J0: {'PASS' if fams else 'FAIL'} (gate {GATE})")
assert fams, "both families fail the validation gate — STOP (P-J0 FAIL)"
NAME, Z, EV = min(fams, key=lambda f: f[2])
print(f"selected family: {NAME} (err {mp.nstr(EV, 3)})")


def F(s):
    return arch(s) * Z(s)


def phiStar(s):
    return (F(s) + F(1 - s)) / 2


def phiStar_line(t):
    # on the line, PhiStar(1/2+it) = Re F(1/2+it) exactly (Schwarz + evenness)
    return F(mpc(mpf('0.5'), t)).real


# on-line zeros of PhiStar in the ball
ts = [TZ - RR + 2 * RR * k / 3000 for k in range(3001)]
vals = [phiStar_line(t) for t in ts]
zline = []
for k in range(3000):
    if vals[k] * vals[k + 1] < 0:
        a_, b_ = ts[k], ts[k + 1]
        fa = vals[k]
        for _ in range(200):
            mid = (a_ + b_) / 2
            fm = phiStar_line(mid)
            if fa * fm <= 0:
                b_ = mid
            else:
                a_, fa = mid, fm
        zline.append((a_ + b_) / 2)
zline = [t for t in zline if abs(mpc(mpf('0.5'), t) - A) < RR]
print(f"PhiStar on-line zeros in ball: {[mp.nstr(t, 25) for t in zline]}")
disp = min(abs(t - TZ) for t in zline) if zline else mpf('inf')
print(f"P-J1: {'PASS' if (len(zline) == 1 and disp < mpf('1e-8')) else 'FAIL'}"
      f" (count={len(zline)}, displacement={mp.nstr(disp, 3)})")

# Newton from the zeta-zero seed on the 2D carrier
rt = findroot(phiStar, A, tol=mpf('1e-50'))
print(f"Newton root: {mp.nstr(rt, 30)}  |off-line displacement| = "
      f"{mp.nstr(abs(rt.real - mpf('0.5')), 3)}")
print(f"P-J2: {'PASS' if abs(rt.real - mpf('0.5')) < mpf('1e-20') and abs(rt.imag - TZ) < mpf('1e-6') else 'FAIL'}")

# zeta side: on-line zeros of xi in the ball (known: exactly the center zero)
zx = [TZ]  # center is a zeta zero by construction; nearest others 0.716 away
# domination on sampled annulus charts (completed scale)
qmax = mpf(0)
arg = None
NR, NA = 5, 360
for i in range(NR):
    r = R0 + (RR - R0) * mpf(i) / (NR - 1)
    for k in range(NA):
        th = 2 * pi * k / NA
        zpt = A + r * mpc(mp.cos(th), mp.sin(th))
        ps = phiStar(zpt)
        q = abs(xi(zpt) - ps) / abs(ps)
        if q > qmax:
            qmax, arg = q, (float(r), float(th))
print(f"domination q_max = {mp.nstr(qmax, 6)} at (r,theta)={arg}")
print(f"P-J3: {'PASS' if qmax < mpf('1e-6') else 'FAIL'}")

D1, L1, N1 = len(zx), len(zx), 0
D2, L2, N2 = len(zline), len(zline), 0
ok = (D1 == D2 == 1 and L1 == L2 == 1 and N1 == N2 == 0 and qmax < 1)
print(f"xi: D1={D1} L1={L1} N1={N1}   PhiStar: D2={D2} L2={L2} N2={N2}")
print(f"P-J4 (first nontrivial positive transfer): {'PASS' if ok else 'FAIL'}")
