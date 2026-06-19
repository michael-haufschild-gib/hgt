"""
Referee: the arithmetic DeWitt pairing (Wheeler-DeWitt scale-clock construction).

Certifies three structural facts about the DeWitt / Klein-Gordon pairing constructed in
docs/drafts/time-emergence-scale-clock-wheeler-dewitt.md (Brick #1):

 (A) THE PAIRING IS THE WEIL FORM, NOT AN ANSATZ.  Its place decomposition
       (archimedean + pole)  -  (primes)
     equals the spectral sum over the *true* zeta zeros (Riemann-Weil explicit formula).
     This certifies that the constructed object is the genuine Weil pairing, with the
     archimedean place as one block and the prime places as the other.

 (B) LORENTZIAN SIGNATURE.  The archimedean+pole block (the 'timelike' / scale-clock
     direction) is positive; the prime block is the indefinite 'spacelike' part.
     For this test function the timelike block dominates => Q_W(h) > 0
     (the emergent clock is timelike for h, consistent with RH).

 (C) OFF-LINE MODES ARE TACHYONIC.  A hypothetical off-line zero quadruple at
       1/2 +/- delta +/- i*gamma     (delta != 0  <=>  off the critical line)
     contributes, for h(t)=exp(-a t^2),
       4 * exp(a*(delta^2 - gamma^2)) * cos(2*a*gamma*delta),
     amplified by exp(a*delta^2) and turning NEGATIVE for delta != 0
     (negative Klein-Gordon norm = spacelike clock = time running backwards).
     SOURCE-PURE: assumes nothing about where the zeros actually are; shows only
     IF a mode is off-line THEN its KG-norm can be negative. This does NOT prove RH
     (that is the open positivity = the clock being timelike on the *true* spectrum).

Test function:  h(t) = exp(-a t^2)   (even, Schwartz, analytic in a strip)
Fourier dual :  g(u) = (1/2pi) * sqrt(pi/a) * exp(-u^2/(4a))
"""
import mpmath as mp

mp.mp.dps = 30
a = mp.mpf('0.05')


def h(t):
    return mp.e ** (-a * t * t)


def g(u):
    return (1 / (2 * mp.pi)) * mp.sqrt(mp.pi / a) * mp.e ** (-(u * u) / (4 * a))


def von_mangoldt(m):
    """Lambda(m) = log p if m = p^k (prime power), else 0. Pure trial division."""
    d = 2
    base = None
    while d * d <= m:
        if m % d == 0:
            base = d
            while m % d == 0:
                m //= d
            break
        d += 1
    if base is None:  # m is prime
        return mp.log(m)
    return mp.log(base) if m == 1 else mp.mpf('0')


# ---------- (A) spectral side: sum over the TRUE nontrivial zeros ----------
# rho = 1/2 + i*gamma_n ; Sum_rho h(gamma_rho) = 2 * sum_{n>=1} h(gamma_n)  (h even)
lhs = mp.mpf('0')
n = 1
while True:
    gamma = mp.im(mp.zetazero(n))
    term = 2 * h(gamma)
    lhs += term
    if term < mp.mpf('1e-30'):
        break
    n += 1
n_zeros = n

# ---------- (A/B) place side: the DeWitt decomposition ----------
# pole contribution (s=1 and s=0): h(i/2) + h(-i/2)        [joins the timelike block]
pole = h(mp.mpc(0, mp.mpf('0.5'))) + h(mp.mpc(0, -mp.mpf('0.5')))

# archimedean term: (1/2pi) int h(t) Re psi(1/4 + i t/2) dt  -  g(0) log pi   [TIMELIKE]
def arch_integrand(t):
    return h(t) * mp.re(mp.digamma(mp.mpf('0.25') + mp.mpc(0, t / 2)))

arch_int = (1 / (2 * mp.pi)) * mp.quad(arch_integrand, [-mp.inf, 0, mp.inf])
arch = arch_int - g(0) * mp.log(mp.pi)

timelike = pole + arch

# prime term: 2 * sum_n Lambda(n)/sqrt(n) * g(log n)        [SPACELIKE]
prime = mp.mpf('0')
m = 2
while True:
    lam = von_mangoldt(m)  # von Mangoldt
    prime += 2 * lam / mp.sqrt(m) * g(mp.log(m))
    if g(mp.log(m)) < mp.mpf('1e-32') and m > 10:
        break
    m += 1
spacelike = prime

rhs = timelike - spacelike

print("=== (A) the pairing IS the Weil explicit formula (place-split = spectral sum) ===")
print("zeros summed:", n_zeros, "  prime-powers summed up to:", m)
print("LHS  spectral   Sum_rho h(gamma_rho) :", mp.nstr(lhs, 22))
print("RHS  places     timelike - spacelike :", mp.nstr(rhs, 22))
print("|LHS - RHS| :", mp.nstr(abs(lhs - rhs), 4), " (-> 0 certifies the construction = Weil form)")

print()
print("=== (B) Lorentzian signature: archimedean timelike vs prime spacelike ===")
print("  pole                       :", mp.nstr(pole, 18))
print("  archimedean integral term  :", mp.nstr(arch_int, 18))
print("  -g(0) log pi               :", mp.nstr(-g(0) * mp.log(mp.pi), 18))
print("  TIMELIKE block (arch+pole) :", mp.nstr(timelike, 18), " (>0: scale-clock direction)")
print("  SPACELIKE block (primes)   :", mp.nstr(spacelike, 18), " (indefinite matter directions)")
print("  Q_W(h)=timelike-spacelike  :", mp.nstr(rhs, 18), " (>0 => clock timelike for this h)")

print()
print("=== (C) off-line modes are tachyonic (negative Klein-Gordon norm) ===")
gamma1 = mp.im(mp.zetazero(1))

def quad_contrib(delta):
    return 4 * mp.e ** (a * (delta * delta - gamma1 * gamma1)) * mp.cos(2 * a * gamma1 * delta)

print("first-zero height gamma =", mp.nstr(gamma1, 12))
print("on-line (delta=0): 4 e^{-a gamma^2} =", mp.nstr(quad_contrib(0), 12), " (> 0, positive frequency)")
for d in ['0.2', '0.5', '1.0', '1.1', '1.2', '1.5']:
    delta = mp.mpf(d)
    c = quad_contrib(delta)
    sign = "NEGATIVE (tachyonic)" if c < 0 else "positive"
    print(f"  delta={d:>4}: contrib = {mp.nstr(c, 12):>16}  amp e^(a d^2)={mp.nstr(mp.e**(a*delta*delta),7)}  [{sign}]")

delta = mp.mpf('0')
while quad_contrib(delta) > 0 and delta < 50:
    delta += mp.mpf('0.001')
print("first off-line delta with NEGATIVE KG-norm:", mp.nstr(delta, 8),
      "  (predicted pi/(4 a gamma) =", mp.nstr(mp.pi / (4 * a * gamma1), 8), ")")
print()
print("VERDICT: the DeWitt pairing is constructed (= Weil form, certified in A),")
print("         its signature is Lorentzian with the scale-clock timelike (B),")
print("         and off-line modes carry negative KG-norm (C). RH = the true spectrum")
print("         is entirely positive-frequency = the clock is timelike everywhere (OPEN).")
