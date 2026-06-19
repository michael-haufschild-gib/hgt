import mpmath as mp
mp.mp.dps = 40

# The completed archimedean factor for zeta: Gamma_R(s) = pi^{-s/2} Gamma(s/2).
def GammaR(s): return mp.pi**(-s/2) * mp.gamma(s/2)

# Riemann xi: xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)  -- entire, xi(s)=xi(1-s).
def xi(s): return mp.mpf('0.5') * s * (s-1) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)

print("=== The archimedean lane: rescaling rule, the weld, the diagonal ===")
# (1) The infinity-lane's rescaling rule: Gamma_R(s+2) = (s/2pi) Gamma_R(s)  -- first-order DIFFERENCE,
#     step 2, with a POLYNOMIAL coefficient s/(2pi) (the new ingredient vs the primes' geometric coeff).
print("\n(1) infinity-lane difference rule  Gamma_R(s+2) = (s/2pi) Gamma_R(s):")
for s in [mp.mpf('1.3')+0.7j, mp.mpf('0.5')+14.13j, mp.mpf('-0.4')+3.1j]:
    lhs = GammaR(s+2); rhs = (s/(2*mp.pi))*GammaR(s)
    print(f"   s={mp.nstr(s,5):>16}:  |LHS-RHS| = {mp.nstr(abs(lhs-rhs),3)}")

# (2) The weld: xi(s)=xi(1-s).  The ONE equation tying the prime product to the archimedean factor.
print("\n(2) the weld (functional equation)  xi(s) = xi(1-s):")
for s in [mp.mpf('2.0')+0j, mp.mpf('0.5')+14.134725j, mp.mpf('0.3')+5.0j, mp.mpf('-1.2')+2.4j]:
    print(f"   s={mp.nstr(s,6):>18}:  |xi(s)-xi(1-s)| = {mp.nstr(abs(xi(s)-xi(1-s)),3)}")

# (3) The shift IS the diagonal of all prime rescalings: s->s+1 sends x_p=p^{-s} to (1/p) x_p, every p.
print("\n(3) shift s->s+1 = simultaneous prime rescalings  p^{-(s+1)} = (1/p) p^{-s}:")
s = mp.mpf('0.5')+14.13j
for p in [2,3,5,7]:
    lhs = mp.mpf(p)**(-(s+1)); rhs = (mp.mpf(1)/p)*mp.mpf(p)**(-s)
    print(f"   p={p}:  |p^-(s+1) - (1/p)p^-s| = {mp.nstr(abs(lhs-rhs),3)}")

# (4) A zero on the shore: at a genuine zero rho=1/2+i*gamma, xi(rho)=0 AND |w|=1 (w=1-1/rho).
print("\n(4) first zero on the shore: xi(rho)=0 and |w_rho|=1 (w=1-1/rho):")
rho = mp.mpf('0.5') + 1j*mp.mpf('14.134725141734693790')
w = 1 - 1/rho
print(f"   |xi(rho)| = {mp.nstr(abs(xi(rho)),3)}   |w_rho| = {mp.nstr(abs(w),20)}")
print("\n# infinity-lane rule, weld, and shift=diagonal all hold to ~1e-38; the genuine zero sits on the unit circle.")
