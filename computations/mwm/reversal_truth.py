#!/usr/bin/env python3
"""
Task #147 certification — the TRUE size of the ledger reversal at C0 ~ 1/2.

Doc 37 Lemma H bounds the convexity-pairing reversal termwise by 200*C0^2; the
honest termwise refold (doc 39 SS2) cannot go below O(C0) because the (F4)
half-gap position floor and the maximal-drop mismatch stack multiplicatively in a
termwise bound although they consume the SAME drop budget (Sum ahead drops <=
delta/2). Decision question (not settleable by bounding technique): is the TRUE
reversal at C0 = 1/2 (c = 2 model fields, the actual-carrier class) below the
march cushion 2, or can the march genuinely stall in bulk?

Objects (indices transcribed from the machine-checked ledger_regroup,
LedgerIdentity.lean; f(x) = coth(x/2), t 1-indexed):
  gain_k  = f(t[i+2]-t[i+1-k]-s) - f(t[i+1]-t[i-k]-s)      k = 0..i-1   (>= 0)
  loss_j  = f(t[i+3+j]-t[i+2]+s) - f(t[i+2+j]-t[i+1]+s)    j = 0..d-i-3 (>= 0)
  extras  = f(t[i+2]-t[1]-s) + f(t[d]-t[i+1]+s)
  DeltaG  = extras + Sum gain - Sum loss                    (identity check)
  reversal(s) = Sum_k max(loss_k - gain_k, 0)  (matched k; one-sided i has
                fewer ahead than behind, all losses matched)

Model field: t_j = c*H_j (harmonic), log-gaps delta_j = c/(j+1), C0 ~ 1/c.
Grid: c in {2,3,4,6,8}; d in {150,400}; i in {ceil((d-1)/2), 2d/3, floor(0.85d)};
s/delta in {0.10, 0.20, 1/3, 0.45, 0.49}, delta = t[i+2]-t[i+1].

PRE-REGISTERED (before first run):
  P-R4 (prior 0.90): identity DeltaG = extras + gains - losses to 1e-18 at every
       grid point (validates transcription against the Lean identity).
  P-R1 (prior 0.65): max over the s-grid of reversal < 2 at c = 2 for ALL bulk
       (i,d) grid points  ==> the C0 = 1/2 gap is bounding TECHNIQUE, not truth:
       invest in the budget-coupled (transport/continuum) route; per-carrier
       march certification is viable at c = 2.
       FAIL ==> the march can genuinely stall at c = 2 in bulk; re-cut the
       (S-mono) claim for actual carriers around the tip cushion.
  P-R2 (prior 0.80): max_s reversal < 1 at c = 4 (theorem-range sanity).
  P-R3 (prior 0.60): log-log slope of max_s reversal against C0 = 1/c across
       c = {2,3,4,6,8} (at d = 400, i = 2d/3) is >= 1.7  ==> truth is ~C0^2;
       the first-order-in-C0 appearance of honest termwise folds is artifact.
"""
from mpmath import mp, mpf, coth, log

mp.dps = 30


def field(c, d):
    t = [mpf(0)] * (d + 1)
    for j in range(2, d + 1):
        t[j] = t[j - 1] + mpf(c) / j          # delta_j = c/(j+1) after shift; any
    return t                                   # harmonic-type c/j field works


def f(x):
    return coth(x / 2)


def ledger(t, d, i, s):
    gains = [f(t[i + 2] - t[i + 1 - k] - s) - f(t[i + 1] - t[i - k] - s)
             for k in range(0, i)]
    # positive losses: f(new ahead) - f(old ahead) >= 0 (the Lean j-sum terms
    # are the NEGATIVE of these; first run had the sign slip, P-R4 caught it)
    losses = [f(t[i + 3 + j] - t[i + 2] + s) - f(t[i + 2 + j] - t[i + 1] + s)
              for j in range(0, d - i - 2)]
    extras = f(t[i + 2] - t[1] - s) + f(t[d] - t[i + 1] + s)
    dG = extras + sum(gains) - sum(losses)
    # direct evaluation for the identity check
    def G(ii, ss):
        a = sum(f(t[ii + 1] - t[ii - k] - ss) for k in range(0, ii))
        b = sum(f(t[ii + 2 + j] - t[ii + 1] + ss) for j in range(0, d - ii - 1))
        return a - f(ss) - b
    dG_direct = G(i + 1, s) - G(i, s)
    rev = sum(max(l - g, mpf(0)) for l, g in zip(losses, gains))
    return dG, dG_direct, extras, rev


if __name__ == "__main__":
    worst_id = mpf(0)
    results = {}
    for c in (2, 3, 4, 6, 8):
        for d in (150, 400):
            t = field(c, d)
            for i in (max((d - 1 + 1) // 2, 2), (2 * d) // 3, (85 * d) // 100):
                delta = t[i + 2] - t[i + 1]
                maxrev = mpf(0)
                for frac in ('0.10', '0.20', '0.3333333', '0.45', '0.49'):
                    s = mpf(frac) * delta
                    dG, dGd, ex, rev = ledger(t, d, i, s)
                    worst_id = max(worst_id, abs(dG - dGd))
                    maxrev = max(maxrev, rev)
                results[(c, d, i)] = maxrev
                print(f"c={c} d={d} i={i} delta={float(delta):.4f}: "
                      f"max_s reversal = {float(maxrev):.5f}")
    print(f"\nP-R4 identity worst |dG - direct| = {float(worst_id):.3e} "
          f"{'PASS' if worst_id < mpf('1e-18') else 'FAIL'}")
    c2 = [v for (c, d, i), v in results.items() if c == 2]
    print(f"P-R1 c=2 all max_s reversal < 2: "
          f"{'PASS' if all(v < 2 for v in c2) else 'FAIL'}  "
          f"(max = {float(max(c2)):.4f})")
    c4 = [v for (c, d, i), v in results.items() if c == 4]
    print(f"P-R2 c=4 all max_s reversal < 1: "
          f"{'PASS' if all(v < 1 for v in c4) else 'FAIL'}  "
          f"(max = {float(max(c4)):.4f})")
    xs, ys = [], []
    for c in (2, 3, 4, 6, 8):
        d = 400
        i = (2 * d) // 3
        v = results[(c, d, i)]
        if v > 0:
            xs.append(log(mpf(1) / c))
            ys.append(log(v))
    n = len(xs)
    if n >= 2:
        xb = sum(xs) / n
        yb = sum(ys) / n
        slope = (sum((x - xb) * (y - yb) for x, y in zip(xs, ys))
                 / sum((x - xb) ** 2 for x in xs))
        print(f"P-R3 log-log slope rev vs C0 (d=400, i=2d/3): "
              f"{float(slope):.3f}  {'PASS' if slope >= mpf('1.7') else 'FAIL'}")


# --- Extension run (pre-registered AFTER main run, BEFORE this run) ---
# Main-run finding: reversal is C0-independent, concentrated at the F1 edge
# i ~ d/2. New predictions:
#   P-R5 (prior 0.5): d-trend at the edge (i = ceil((d-1)/2), c = 2):
#        rev grows at most logarithmically; register rev(d=2500) < 0.35.
#   P-R6 (prior 0.7): i-profile at d = 400, c = 2: rev monotone decreasing in
#        i/d on {0.50, 0.52, 0.55, 0.60, 0.66, 0.75}, and <= 0.25 throughout.
# Also record argmax_s (which band the reversal threatens).
def profile():
    for c, d, ii_list in ((2, 150, None), (2, 400, None), (2, 1000, None),
                          (2, 2500, None)):
        t = field(c, d)
        i = (d - 1 + 1) // 2
        delta = t[i + 2] - t[i + 1]
        best, sarg = mpf(0), None
        for frac in ('0.10', '0.20', '0.3333333', '0.45', '0.49'):
            s = mpf(frac) * delta
            _, _, _, rev = ledger(t, d, i, s)
            if rev > best:
                best, sarg = rev, frac
        print(f"P-R5 edge d={d}: rev = {float(best):.5f} at s/delta = {sarg}")
    d = 400
    t = field(2, d)
    for fr in ('0.50', '0.52', '0.55', '0.60', '0.66', '0.75'):
        i = int(float(fr) * d)
        delta = t[i + 2] - t[i + 1]
        best, sarg = mpf(0), None
        for frac in ('0.10', '0.20', '0.3333333', '0.45', '0.49'):
            s = mpf(frac) * delta
            _, _, _, rev = ledger(t, d, i, s)
            if rev > best:
                best, sarg = rev, frac
        print(f"P-R6 i/d={fr}: rev = {float(best):.5f} at s/delta = {sarg}")


# --- Closed-form pass (pre-registered BEFORE this run) ---
# Continuum reversal R(theta,c,s) = int_0^{xiA} c*xi*[ W(c*log(1+xi)+s)/(1+xi)
#   - W(-c*log(1-xi)-s)/(1-xi) ]^+ dxi,  W(x) = (1/2)csch(x/2)^2, xiA = (1-th)/th.
# Hand-derived: at c = 2, s = 0 the integrand is 8 xi^2/(4-xi^2)^2 and
#   R(th,2,0) = 4 xiA/(4-xiA^2) - log((2+xiA)/(2-xiA));  R(1/2,2,0) = 4/3 - log 3.
# P-R9 (prior 0.9): closed form = direct mpmath quad of the exact integrand to
#      1e-12 at th in {0.5, 0.6, 0.75} (checks the calculus).
# P-R8 (prior 0.6): sup_{c>=2} R(1/2,c,0) is attained at c in (2,4) and is < 0.26.
# P-R7 (prior 0.8): discrete ledger reversal at d = 10000, c = 2, i = d/2,
#      s = 0.001*delta lies in [0.2330, 0.2360] (the closed form +- finite-d).
def W(x):
    from mpmath import csch
    return csch(x / 2) ** 2 / 2


def R_integrand(c, s, xi):
    return c * xi * (W(c * log(1 + xi) + s) / (1 + xi)
                     - W(-c * log(1 - xi) - s) / (1 - xi))


def closed_form(theta):
    xiA = (1 - theta) / theta
    return 4 * xiA / (4 - xiA ** 2) - log((2 + xiA) / (2 - xiA))


def closed_pass():
    from mpmath import quad
    print("P-R9:")
    for th in (mpf('0.5'), mpf('0.6'), mpf('0.75')):
        xiA = (1 - th) / th
        num = quad(lambda x: max(R_integrand(2, mpf(0), x), mpf(0)), [0, xiA])
        cf = closed_form(th)
        print(f"  theta={float(th)}: quad = {float(num):.12f}  "
              f"closed = {float(cf):.12f}  diff = {float(abs(num-cf)):.2e}")
    print(f"  R(1/2,2,0) = 4/3 - log 3 = {float(mpf(4)/3 - log(3)):.9f}")
    print("P-R8 sup over c at theta = 1/2:")
    best, bc = mpf(0), None
    for cc in ('2', '2.25', '2.5', '2.75', '3', '3.25', '3.5', '4', '5', '6',
               '8', '12'):
        c = mpf(cc)
        v = quad(lambda x: max(R_integrand(c, mpf(0), x), mpf(0)), [0, 1])
        if v > best:
            best, bc = v, cc
        print(f"  c={cc}: R = {float(v):.6f}")
    print(f"  sup = {float(best):.6f} at c = {bc}  "
          f"{'P-R8 PASS' if 2 < float(bc) < 4 and best < mpf('0.26') else 'P-R8 FAIL'}")
    d, c = 10000, 2
    t = field(c, d)
    i = d // 2
    delta = t[i + 2] - t[i + 1]
    _, _, _, rev = ledger(t, d, i, mpf('0.001') * delta)
    ok = mpf('0.2330') < rev < mpf('0.2360')
    print(f"P-R7 discrete d=10000 s=0.001delta: rev = {float(rev):.6f}  "
          f"{'PASS' if ok else 'FAIL'}")


# --- (B4-a) certified grid (pre-registered BEFORE this run) ---
# Unified form (doc 41 SS2): R(1/2,c,0) = c*J1(c) - c*J2(c),
#   J1 = int_0^{log2} 2 sinh(z/2)^2 csch(cz/2)^2 dz,
#   J2 = int_{log2}^inf (1-e^-z) (1/2) csch(cz/2)^2 dz.
# Positivity lemma (doc 41 SS1) makes the + clip vacuous for c >= 2, so this IS R.
# Tail bound R(c) <= 8.16/c^2 for c >= 3  ==> < 1/4 for c >= 6.
# Lipschitz on [2,6]: |R'(c)| <= L0 = 1.6 (doc 41 SS2 fold).
# P-R11 (prior 0.9): unified = direct xi-integrand quad to 1e-10 at c in
#   {2, 2.5, 4}; and unified(2) = 4/3 - log 3 to 1e-12 (partial-fraction check).
# P-R10 (prior 0.85): grid c = 2(0.0025)6: max_c [R_hat(c) + L0*eps/2] < 1/4,
#   i.e. max R_hat < 0.248.  PASS completes (B4-a): sup_{c>=2} R(1/2,c,0) < 1/4.
def R_unified(c):
    from mpmath import quad, sinh, csch, exp as mexp
    c = mpf(c)
    j1 = quad(lambda z: 2 * sinh(z / 2) ** 2 * csch(c * z / 2) ** 2,
              [0, mpf('0.05'), mpf('0.35'), log(2)])
    j2 = quad(lambda z: (1 - mexp(-z)) * csch(c * z / 2) ** 2 / 2,
              [log(2), 3, 8, mp.inf])
    return c * (j1 - j2)


def grid_pass():
    from mpmath import quad
    mp.dps = 25
    print("P-R11:")
    for cc in ('2', '2.5', '4'):
        c = mpf(cc)
        direct = quad(lambda x: R_integrand(c, mpf(0), x),
                      [mpf('1e-6'), mpf('0.01'), mpf('0.5'), 1])
        uni = R_unified(c)
        print(f"  c={cc}: unified = {float(uni):.12f}  "
              f"|diff| = {float(abs(uni - direct)):.2e}")
    v2 = R_unified(2)
    cf = mpf(4) / 3 - log(3)
    print(f"  c=2 vs 4/3-log3: |diff| = {float(abs(v2 - cf)):.2e}")
    best, bc, n = mpf(0), None, 0
    c = mpf(2)
    step = mpf('0.0025')
    while c <= 6 + step / 2:
        v = R_unified(c)
        if v > best:
            best, bc = v, c
        n += 1
        c += step
    guard = best + mpf('1.6') * step / 2
    print(f"P-R10: {n} grid points on [2,6]; max R = {float(best):.9f} at "
          f"c = {float(bc):.4f}; max + L0*eps/2 = {float(guard):.9f}  "
          f"{'PASS' if guard < mpf('0.25') else 'FAIL'}")
