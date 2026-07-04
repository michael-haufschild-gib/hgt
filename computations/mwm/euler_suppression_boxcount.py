#!/usr/bin/env python3
"""
Task #146 — Euler-suppression discrimination test (the missing pincer cell, made
quantitative). Skeleton: structural mutation of truncation_boxcount.py (same box
sweep, same winding engine) + dh_disc_foil.py (same recentered-jet reader shape,
jets by Cauchy trapezoid as in uplane_reader_136.py).

DESIGN. Exact-FE carriers with toggled coefficient structure:
    Phi_a(s) = pi^(-s/2) Gamma(s/2) A_N(s) + pi^(-(1-s)/2) Gamma((1-s)/2) A_N(1-s),
    A_N(s) = sum_{n<=N} a_n n^(-s),  a_n real  ==>  Phi_a(1-s) = Phi_a(s) EXACTLY
and Phi_a real on the critical line — the FE axis is held fixed for EVERY
coefficient choice; only the Euler axis varies:
  E : a_n = 1                       (zeta truncation; run-5 replication baseline)
  M : a_n = f(n), f completely multiplicative, f(p) iid uniform +-1  (HAS Euler
      product; "random character")
  R : a_n iid uniform +-1, a_1 = +1 (same +-1 marginals, NO multiplicative
      dependence structure)
M vs R isolates multiplicativity at matched coefficient statistics. Sweep schedule
N = floor(sqrt(T/2pi)) identical across classes (run-5 convention).
Bands: band1 T in [200,1030) (N = 5..12; few Euler constraints bind — secondary),
band2 T in [5000,5830) (N = 28..30 — PRIMARY band). Boxes sigma in [0.53,1.35],
Dt = 5; count = total winding (right-half off-line zeros, with multiplicity).
Seeds (drawn from scripts/rng CSPRNG, session seed 1920367149821033252, BEFORE any
run): M: 519173902 894929634 969936455 845110651 887867661 356399997 832356436
417209158; R: 812396031 103264158 860208531 513265629 765837507 748916162
124652357 325516467.

PRE-REGISTERED PREDICTIONS (before first run; priors stated):
  P-A (replication gate, prior 0.9): E on band1 reproduces run 5 — total count 5,
      first hit box at T in [220,225).
  P-B (FE alone insufficient, prior 0.7): mean R count on band2 >= 3x the E band2
      count + 1 (off-line zeros appear at a clearly positive rate for iid
      coefficients). If instead R ~ E ~ 0 on band2, the instrument is insensitive
      at this scale — redesign (higher band or larger N), no verdict.
  P-C (EULER SUPPRESSION — the decisive cell, prior 0.45): on band2,
      mean_M(count) <= (1/2) mean_R(count). Dose-response signature: the
      M/R ratio on band2 is SMALLER than on band1 (suppression grows as
      multiplicative constraints bind more indices).
      PASS => first quantitative evidence that multiplicative structure ITSELF
      (not size, not FE) suppresses odd windows: (DISC-fin)'s engine is real;
      next object = which coefficient statistic carries it.
      FAIL (M ~ R) => Euler structure does not act at truncation/window scale;
      (DISC-fin)'s "Euler in the coefficients" needs re-cutting — the arithmetic
      input must enter elsewhere (asymptotic/cofinal, or a_n>0 positivity).
  P-D (reader exactness on the new classes, prior 0.85): for the first refined
      off-line zero of one M carrier and one R carrier, the recentered jet
      sections at t0 read non-real pair count = 1 (disc < 0) at d in {4,6,8},
      n = 0. FALSIFIER: count 0 (blind reader) or >= 2 (spurious pairs) on any —
      kills the (DISC) reader shape beyond the arithmetic carriers.
  P-E (zeta large-d SPUR stability, card #146(a), prior 0.8): exact-xi reader at
      the two banked windows t0 = 85.6993484853775922 (run 4) and
      t0 = 221.07888411131592586 (runs 5/6): pair count 0 (disc > 0) at
      d in {10,12,16}, n in {0,1}. FALSIFIER: a spurious pair at large d =>
      the (SPUR) mechanism degrades with degree — load-bearing for (SPUR-R).
Settled by reasoning, NOT run (anti-theatre): the Revesz/BDR foil itself (Euler,
no FE) admits no real carrier — Phi needs the FE for reality on the line (doc 19
S5); the reader is structurally nonexistent there. Its pincer role is already
carried by doc 14 S6.
"""
import sys
from multiprocessing import Pool

from mpmath import (mp, mpc, mpf, pi, gamma as Gamma, sqrt, floor, fabs, arg,
                    findroot, binomial, polyroots, re, im, exp, zeta, nstr)

I = mpc(0, 1)

M_SEEDS = [519173902, 894929634, 969936455, 845110651,
           887867661, 356399997, 832356436, 417209158]
R_SEEDS = [812396031, 103264158, 860208531, 513265629,
           765837507, 748916162, 124652357, 325516467]
BANDS = {1: (200, 1030), 2: (5000, 5830)}
NMAX = 31


def lcg(seed):
    s = seed
    while True:
        s = (6364136223846793005 * s + 1442695040888963407) % (1 << 64)
        yield 1 if (s >> 33) & 1 else -1


def primes_upto(n):
    sieve = [True] * (n + 1)
    ps = []
    for p in range(2, n + 1):
        if sieve[p]:
            ps.append(p)
            for q in range(p * p, n + 1, p):
                sieve[q] = False
    return ps


def coeffs(cls, seed, nmax=NMAX):
    if cls == 'E':
        return [1] * (nmax + 1)
    g = lcg(seed)
    a = [0] * (nmax + 1)
    a[1] = 1
    if cls == 'R':
        for n in range(2, nmax + 1):
            a[n] = next(g)
        return a
    fp = {p: next(g) for p in primes_upto(nmax)}
    for n in range(2, nmax + 1):
        v, m = 1, n
        for p in fp:
            while m % p == 0:
                v *= fp[p]
                m //= p
        a[n] = v
    return a


def make_phi(a, N):
    def A(s):
        return sum(a[n] * mpf(n) ** (-s) for n in range(1, N + 1))

    def phi(s):
        return (pi ** (-s / 2) * Gamma(s / 2) * A(s)
                + pi ** (-(1 - s) / 2) * Gamma((1 - s) / 2) * A(1 - s))
    return phi


def winding(g, s_lo, s_hi, t_lo, t_hi, m=160):
    pts = []
    for k in range(m):
        pts.append(mpc(s_lo + (s_hi - s_lo) * k / m, t_lo))
    for k in range(m):
        pts.append(mpc(s_hi, t_lo + (t_hi - t_lo) * k / m))
    for k in range(m):
        pts.append(mpc(s_hi - (s_hi - s_lo) * k / m, t_hi))
    for k in range(m):
        pts.append(mpc(s_lo, t_hi - (t_hi - t_lo) * k / m))
    pts.append(pts[0])
    tot = mpf(0)
    prev = arg(g(pts[0]))
    suspicious = False
    for p in pts[1:]:
        aa = arg(g(p))
        d = aa - prev
        while d > pi:
            d -= 2 * pi
        while d < -pi:
            d += 2 * pi
        if fabs(d) > mpf('2.8'):
            suspicious = True
        tot += d
        prev = aa
    w = int(mp.nint(tot / (2 * pi)))
    return w, suspicious


def sweep(job):
    cls, seed, band = job
    mp.dps = 25
    t_lo, t_hi = BANDS[band]
    a = coeffs(cls, seed)
    hits = []
    T = mpf(t_lo)
    while T < t_hi:
        N = int(floor(sqrt(T / (2 * pi))))
        phi = make_phi(a, N)
        w, susp = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5)
        if susp:
            w, _ = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5, m=320)
        if w != 0:
            hits.append((float(T), N, w))
        T += 5
    return cls, seed, band, hits


def cauchy_jets(F, t0, mmax, r=3, K=512):
    # gamma_m = m! / (2 pi i) * contour integral; trapezoid on |t - t0| = r
    vals = [F(t0 + r * exp(2 * pi * I * mpf(k) / K)) for k in range(K)]
    jets = []
    fact = mpf(1)
    for m_ in range(mmax + 1):
        if m_ > 0:
            fact *= m_
        s = sum(vals[k] * exp(-2 * pi * I * mpf(m_ * k) / K) for k in range(K))
        jets.append(fact * s / (K * mpf(r) ** m_))
    return jets


def pair_counts(jets_real, ds, ns, thresh=mpf('1e-18')):
    out = {}
    for d in ds:
        for n in ns:
            cf = [binomial(d, j) * jets_real[n + j] for j in range(d, -1, -1)]
            big = max(fabs(c) for c in cf)
            while len(cf) > 1 and fabs(cf[0]) < big * mpf('1e-40'):
                cf = cf[1:]
            roots = polyroots(cf, maxsteps=400, extraprec=400)
            nr = sum(1 for rt in roots if fabs(im(rt)) / (1 + fabs(rt)) > thresh)
            assert nr % 2 == 0
            out[(d, n)] = nr // 2
    return out


def reader_on_hit(cls, seed, T0, N, label):
    mp.dps = 60
    a = coeffs(cls, seed)
    phi = make_phi(a, N)
    s0 = mpc('0.8', T0 + mpf('2.5'))
    root = findroot(phi, s0, solver='muller', tol=mpf('1e-40'))
    t0 = im(root)
    sig = re(root)
    print(f"  {label}: refined zero {nstr(sig, 10)} + {nstr(t0, 14)}i  "
          f"|Phi| = {nstr(fabs(phi(root)), 3)}")
    if not (mpf('0.53') < sig < mpf('1.35') and T0 - 1 < t0 < T0 + 6):
        print(f"  {label}: root left the box — SKIP reader")
        return None

    def Xi(t):
        return phi(mpf(1) / 2 + I * t)

    jets = cauchy_jets(Xi, t0, 18)
    noise = max(fabs(im(j)) / (1 + fabs(j)) for j in jets)
    print(f"  {label}: jet Im-noise = {nstr(noise, 3)}")
    counts = pair_counts([re(j) for j in jets], (4, 6, 8), (0,))
    explor = pair_counts([re(j) for j in jets], (10, 12, 16), (0,))
    print(f"  {label}: P-D counts {sorted(counts.items())}  "
          f"exploratory {sorted(explor.items())}")
    return counts


def phase_sweep():
    jobs = [('E', 0, 1), ('E', 0, 2)]
    jobs += [('M', s, b) for s in M_SEEDS for b in (1, 2)]
    jobs += [('R', s, b) for s in R_SEEDS for b in (1, 2)]
    with Pool(16) as pool:
        results = pool.map(sweep, jobs)
    per = {}
    for cls, seed, band, hits in results:
        tot = sum(h[2] for h in hits)
        per[(cls, seed, band)] = (tot, hits)
        print(f"{cls} seed={seed} band{band}: count = {tot}  hits = {hits}")
    for band in (1, 2):
        e = per[('E', 0, band)][0]
        mm = [per[('M', s, band)][0] for s in M_SEEDS]
        rr = [per[('R', s, band)][0] for s in R_SEEDS]
        mbar = sum(mm) / len(mm)
        rbar = sum(rr) / len(rr)
        print(f"BAND{band}: E = {e}  M mean = {mbar:.3f} {mm}  "
              f"R mean = {rbar:.3f} {rr}")
    # uniqueness audit (band coefficient collisions among M seeds)
    for band, nm in ((1, 12), (2, 30)):
        vecs = {tuple(coeffs('M', s)[:nm + 1]) for s in M_SEEDS}
        print(f"band{band}: unique M coefficient vectors = {len(vecs)}/8")
    return per


def phase_reader(per):
    done = {'M': 0, 'R': 0}
    for (cls, seed, band), (tot, hits) in sorted(per.items()):
        if cls in done and done[cls] < 2 and hits:
            T0, N, w = hits[0]
            reader_on_hit(cls, seed, mpf(T0), N, f"P-D {cls} seed={seed} b{band}")
            done[cls] += 1


def phase_zeta():
    mp.dps = 60

    def Xi(t):
        s = mpf(1) / 2 + I * t
        return s * (s - 1) / 2 * pi ** (-s / 2) * Gamma(s / 2) * zeta(s)

    for t0s in ('85.6993484853775922', '221.07888411131592586'):
        t0 = mpf(t0s)
        jets = cauchy_jets(Xi, t0, 18)
        noise = max(fabs(im(j)) / (1 + fabs(j)) for j in jets)
        counts = pair_counts([re(j) for j in jets], (10, 12, 16), (0, 1))
        ok = all(v == 0 for v in counts.values())
        print(f"P-E t0 = {t0s}: Im-noise = {nstr(noise, 3)}  "
              f"counts {sorted(counts.items())}  {'PASS' if ok else 'FAIL'}")


if __name__ == "__main__":
    phase = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if phase in ('sweep', 'all'):
        per = phase_sweep()
        if phase == 'all':
            phase_reader(per)
    if phase in ('zeta', 'all'):
        phase_zeta()


# --- Q-control extension (pre-registered BEFORE its run, after the main run) ---
# Q: a_n iid uniform +-1 EXCEPT a_(m^2) = +1 forced (and a_1 = 1). This matches the
# M class's MEAN vector exactly (E_f[f(n)] = 1 if n is a square, else 0) while
# destroying all multiplicative dependence.
# P-F (prior 0.5): band2 mean_Q >= 114.5 (= midpoint of measured mean_M = 91 and
# mean_R = 138)  ==> the 10-sigma M-vs-R suppression is carried by multiplicative
# DEPENDENCE, not by the positive-square mean bias. mean_Q < 114.5 ==> the mean
# bias carries it. Seeds (scripts/rng, drawn 2026-07-04 after main run): 736938496
# 332468424 639884945 464857008 16860898 450872636 189292430 375173710.
Q_SEEDS = [736938496, 332468424, 639884945, 464857008,
           16860898, 450872636, 189292430, 375173710]


def coeffs_q(seed, nmax=NMAX):
    import math
    g = lcg(seed)
    a = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        r = math.isqrt(n)
        a[n] = 1 if r * r == n else next(g)
    return a


def phase_q():
    global coeffs
    orig = coeffs

    def patched(cls, seed, nmax=NMAX):
        if cls == 'Q':
            return coeffs_q(seed, nmax)
        return orig(cls, seed, nmax)
    coeffs = patched
    import euler_suppression_boxcount as m
    m.coeffs = patched
    jobs = [('Q', s, b) for s in Q_SEEDS for b in (1, 2)]
    with Pool(16) as pool:
        results = pool.map(sweep_q, jobs)
    per = {}
    for cls, seed, band, hits in results:
        tot = sum(h[2] for h in hits)
        per[(cls, seed, band)] = tot
        print(f"Q seed={seed} band{band}: count = {tot}")
    for band in (1, 2):
        qq = [per[('Q', s, band)] for s in Q_SEEDS]
        print(f"BAND{band}: Q mean = {sum(qq)/len(qq):.3f} {qq}")


def sweep_q(job):
    cls, seed, band = job
    mp.dps = 25
    t_lo, t_hi = BANDS[band]
    a = coeffs_q(seed)
    hits = []
    T = mpf(t_lo)
    while T < t_hi:
        N = int(floor(sqrt(T / (2 * pi))))
        phi = make_phi(a, N)
        w, susp = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5)
        if susp:
            w, _ = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5, m=320)
        if w != 0:
            hits.append((float(T), N, w))
        T += 5
    return cls, seed, band, hits


# --- X-frame extension (pre-registered BEFORE its run, after Q results) ---
# Coherence isolation: a_n = chi_{-4}(n) (real primitive character mod 4; genuinely
# completely multiplicative) run in TWO frames:
#   X-coh:   its own completion  (4/pi)^((s+1)/2) Gamma((s+1)/2) A_N(s) + reflect,
#            AFE length N = floor(sqrt(4T/2pi))   (odd character, epsilon = +1)
#   X-incoh: zeta's frame pi^(-s/2) Gamma(s/2) A_N(s) + reflect, N = floor(sqrt(T/2pi))
# Multiplicativity is IDENTICAL in both; only frame coherence toggles.
# P-G (prior 0.75): X-coh band2 count <= 12 (E-like; L(s,chi_-4) is RH-clean here).
# P-H (prior 0.70): X-incoh band2 count >= 30 (M-like; a true character stream in
#     the WRONG frame behaves like a random multiplicative stream).
# PASS both ==> off-line rate is governed by stream-frame COHERENCE, not by
# multiplicativity: (DISC-fin)'s arithmetic input is the weld (AFE identity),
# re-cutting #130's "Euler structure" clause. FAIL P-H (X-incoh small) ==> true
# characters are clean in any frame — multiplicativity of an actual character IS
# sufficient; FAIL P-G ==> frame story wrong, redesign.

def chi4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


def make_phi_x(coh, N):
    def A(s):
        return sum(chi4(n) * mpf(n) ** (-s) for n in range(1, N + 1) if n % 2)

    if coh:
        def phi(s):
            return ((4 / pi) ** ((s + 1) / 2) * Gamma((s + 1) / 2) * A(s)
                    + (4 / pi) ** ((2 - s) / 2) * Gamma((2 - s) / 2) * A(1 - s))
    else:
        def phi(s):
            return (pi ** (-s / 2) * Gamma(s / 2) * A(s)
                    + pi ** (-(1 - s) / 2) * Gamma((1 - s) / 2) * A(1 - s))
    return phi


def sweep_x(job):
    coh, band = job
    mp.dps = 25
    t_lo, t_hi = BANDS[band]
    hits = []
    T = mpf(t_lo)
    while T < t_hi:
        if coh:
            N = int(floor(sqrt(4 * T / (2 * pi))))
        else:
            N = int(floor(sqrt(T / (2 * pi))))
        phi = make_phi_x(coh, N)
        w, susp = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5)
        if susp:
            w, _ = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5, m=320)
        if w != 0:
            hits.append((float(T), N, w))
        T += 5
    return coh, band, hits


def phase_x():
    jobs = [(c, b) for c in (True, False) for b in (1, 2)]
    with Pool(4) as pool:
        results = pool.map(sweep_x, jobs)
    for coh, band, hits in results:
        tot = sum(h[2] for h in hits)
        tag = 'X-coh' if coh else 'X-incoh'
        print(f"{tag} band{band}: count = {tot}  hits = {hits[:12]}"
              f"{' ...' if len(hits) > 12 else ''}")
