# Diagnostic: where does the reflected zero actually live in the (c,d) family?
# 1. Verify classical FE Lambda(s,chi) = eps * Lambda(1-s,chibar) numerically (eps s-independent?).
# 2. Compute required ratio r = c/d killing f at the reflected points 1-rho and 1-conj(rho);
#    check |r| (on the k-circle iff |r| = 1).
from mpmath import mp, mpc, mpf, zeta, gamma, pi, sqrt, findroot, fabs, atan, tan

mp.dps = 30
i = mpc(0, 1)
chi = {1: mpc(1), 2: i, 3: -i, 4: mpc(-1)}
kappa = (sqrt(10 - 2*sqrt(5)) - 2) / (sqrt(5) - 1)

def L(s, bar=False):
    tot = mpc(0)
    for a in range(1, 5):
        c = chi[a].conjugate() if bar else chi[a]
        tot += c * zeta(s, mpf(a)/5)
    return 5**(-s) * tot

def W(s):  # completion for odd character mod 5
    return (5/pi)**((s+1)/2) * gamma((s+1)/2)

def Lam(s, bar=False):
    return W(s) * L(s, bar)

# 1. FE check at two points
for s0 in [mpc(0.7, 3.0), mpc(0.3, 11.0)]:
    e1 = Lam(s0) / Lam(1-s0, bar=True)
    e2 = Lam(s0, bar=True) / Lam(1-s0)
    print("s0 =", s0, " eps(chi) cand =", e1, " |.| =", fabs(e1))
    print("            eps(chibar) cand =", e2, " |.| =", fabs(e2))

def f(k, s):
    c = (1 - i*k)/2
    return c * L(s) + c.conjugate() * L(s, bar=True)

rho0 = mpc("0.808517182456637386", "85.6993484853775922")
k1 = kappa + mpf("0.03")
rho1 = findroot(lambda s: f(k1, s), rho0, solver='muller', tol=1e-25)
print("rho(k1) =", rho1)

for name, s0 in [("1-rho", 1-rho1), ("1-conj(rho)", 1-rho1.conjugate())]:
    r = -L(s0, bar=True) / L(s0)   # c/d required for c*L + d*Lbar = 0 at s0
    print(name, ": required r = c/d =", r, "  |r| =", fabs(r))
    # if |r|=1, corresponding real k: r = (1-ik)/(1+ik) => k = i(r-1)/(r+1)
    kk = i*(r-1)/(r+1)
    print("      corresponding k (should be ~real if on k-circle):", kk)
    print("      Moebius prediction was k' =", tan(2*atan(kappa) - atan(k1)))
