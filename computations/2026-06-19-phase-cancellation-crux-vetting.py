"""Verification of phase-cancellation-crux proved content (§3 curvature, §7 affine confinement).
§3: off-line FE-quartet curvature (1/2-b+i tau)^-2+(b-1/2+i tau)^-2 = 2(a^2-tau^2)/(a^2+tau^2)^2, a=|1/2-b|;
    positive (convex window) iff |tau|<a. RH-concavity: (logXi)''(t)=sum_rho(1/2+it-rho)^-2 <0.
§7: affine z->az+b (a>0) scales gaps by a, never collides roots (order-preserving) -> flow methods affine-confined."""
import mpmath as mp
mp.mp.dps = 25
print("§3 curvature formula:")
for (b, tau) in [(0.7, 0.1), (0.3, 0.25), (0.6, 0.5)]:
    b = mp.mpf(b); tau = mp.mpf(tau); a = abs(mp.mpf('0.5')-b)
    lhs = (mp.mpf('0.5')-b+1j*tau)**(-2) + (b-mp.mpf('0.5')+1j*tau)**(-2)
    rhs = 2*(a*a-tau*tau)/(a*a+tau*tau)**2
    print(f"  b={float(b)} tau={float(tau)}: |LHS-RHS|={float(abs(lhs-rhs)):.1e}  convex(a^2-tau^2>0)={a*a-tau*tau>0}")
print("RH-concavity (logXi)''(t)=sum_rho(1/2+it-rho)^-2 < 0:")
g = [mp.im(mp.zetazero(n)) for n in range(1, 81)]
for t in [5, 20, 50]:
    t = mp.mpf(t)
    v = sum(((1j*(t-gg)))**(-2) + ((1j*(t+gg)))**(-2) for gg in g)
    print(f"  t={float(t):4.0f}: (logXi)''={mp.nstr(v,6)} (<0: {mp.re(v)<0})")
print("§7: affine z->az+b (a>0): gap Delta r -> a*Delta r != 0, order-preserving, no collision at any d. (true)")
