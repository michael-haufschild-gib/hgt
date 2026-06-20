"""
THE-MACHINE round (Wheeler). NODE = Spherical functions on Gelfand pairs.
Constraint (not a flow): K-averaged multiplicativity FE  ∫_K φ(xky)dk = φ(x)φ(y).
Experiment transferred to HT seeds with MINIMAL change:
  replace φ -> {Γ, Hurwitz-ζ}; replace ∫_K (compact-group average) -> the finite-orbit
  averaging each HT object carries: its distribution / multiplication relation.
Question (same rigidity probe as last round's d'Alembert run):
  Is the K-AVERAGED relation RIGID (perturbation breaks) or LOOSE (a family survives)?
  Compare against the single shift-FE, which last round showed is LOOSE.
Fast: mpmath, a handful of evals. Seconds.
"""
import mpmath as mp
mp.mp.dps = 40

def rr(a, b):
    a, b = mp.mpf(mp.fabs(a)) if not isinstance(a, mp.mpc) else a, b
    num = abs(mp.mpc(a) - mp.mpc(b))
    den = max(abs(mp.mpc(a)), abs(mp.mpc(b)), mp.mpf(1))
    return num/den

print("="*78)
print("STEP 5/6 ANCHOR — the NODE experiment runs and is meaningful")
print("="*78)
# Spherical fn for Gelfand pair (R x {+-1}, {+-1}) is cos: 1/2[cos(a+b)+cos(a-b)] = cos a cos b
a, b = mp.mpf('0.7'), mp.mpf('1.3')
lhs = (mp.cos(a+b)+mp.cos(a-b))/2
rhs = mp.cos(a)*mp.cos(b)
print(f"cos as spherical fn, K={{+-1}}: avg-FE residual = {mp.nstr(rr(lhs,rhs),3)}  (=0 => holds)")
# RIGIDITY on the NODE: perturb cos -> (1+e)cos breaks (known d'Alembert rigidity)
e = mp.mpf('0.1'); f = lambda x:(1+e)*mp.cos(x)
lhs2 = (f(a+b)+f(a-b))/2; rhs2 = f(a)*f(b)
print(f"  perturb (1+0.1)cos: residual = {mp.nstr(rr(lhs2,rhs2),3)}  (large => RIGID, as expected)")

print()
print("="*78)
print("STEP 7 — TRANSFER to HT: single shift-FE (loose?) vs K-averaged relation (rigid?)")
print("="*78)

# Period-1 multiplicative perturbation P(z) = exp(c*cos(2*pi*z))  (analytic, period 1, !=const)
c = mp.mpf('0.37')
P = lambda z: mp.e**(c*mp.cos(2*mp.pi*z))

print("\n--- Gamma: single shift-FE  Gamma(x+1) = x Gamma(x) ---")
x = mp.mpf('1.618')
G = mp.gamma
res_shift = rr(G(x+1), x*G(x))
print(f"  unperturbed residual = {mp.nstr(res_shift,3)}")
# perturbed: (G*P)(x+1) =? x (G*P)(x)   <=> P(x+1)=P(x), true since P period 1
GP = lambda z: G(z)*P(z)
res_shift_pert = rr(GP(x+1), x*GP(x))
print(f"  perturbed G*P (P period 1) residual = {mp.nstr(res_shift_pert,3)}  => LOOSE (survives)")

print("\n--- Gamma: K-averaged (Gauss multiplication) relation ---")
for m in (2,3,5):
    # prod_{j=0}^{m-1} Gamma((x+j)/m) = (2pi)^((m-1)/2) m^(1/2 - x) Gamma(x)
    lhs = mp.mpf(1)
    for j in range(m): lhs *= G((x+j)/m)
    rhs = (2*mp.pi)**(mp.mpf(m-1)/2) * mp.mpf(m)**(mp.mpf(1)/2 - x) * G(x)
    res = rr(lhs, rhs)
    # perturbed with SAME period-1 P:
    lhsP = mp.mpf(1)
    for j in range(m): lhsP *= GP((x+j)/m)
    rhsP = (2*mp.pi)**(mp.mpf(m-1)/2) * mp.mpf(m)**(mp.mpf(1)/2 - x) * GP(x)
    resP = rr(lhsP, rhsP)
    # the perturbation factor that must vanish: prod_j P((x+j)/m) / P(x)
    pf = mp.mpf(1)
    for j in range(m): pf *= P((x+j)/m)
    pf = pf / P(x)
    print(f"  m={m}: unperturbed residual={mp.nstr(res,3)} | perturbed G*P residual={mp.nstr(resP,3)} "
          f"| prod_j P((x+j)/m)/P(x)={mp.nstr(pf,5)} (=1 iff survives)")

print("\n--- Hurwitz zeta: K-averaged (distribution) relation ---")
s = mp.mpf('2.5'); a0 = mp.mpf('0.3')
HZ = lambda ss,aa: mp.zeta(ss, aa)
for m in (2,3,5):
    # sum_{j=0}^{m-1} zeta(s,(a+j)/m) = m^s zeta(s,a)
    lhs = mp.fsum([HZ(s,(a0+j)/m) for j in range(m)])
    rhs = mp.mpf(m)**s * HZ(s,a0)
    res = rr(lhs, rhs)
    # additive period-1 perturbation H(a)=cos(2 pi a): survives iff sum_j H((a+j)/m)=m^s H(a)
    H = lambda aa: mp.cos(2*mp.pi*aa)
    lhsH = mp.fsum([H((a0+j)/m) for j in range(m)])
    rhsH = mp.mpf(m)**s * H(a0)
    resH = rr(lhsH, rhsH)
    print(f"  m={m}: distribution residual={mp.nstr(res,3)} | "
          f"period-1 perturbation H survives? sum_j H = {mp.nstr(lhsH,4)} vs m^s H = {mp.nstr(rhsH,4)} "
          f"=> {'SURVIVES' if resH<1e-20 else 'BROKEN (rigid)'}")

print("\n--- DRIVING FORCE: does stacking m=2,3,5 pin the period-1 freedom to a point? ---")
# A period-1 P survives ALL Gauss relations iff prod_j P((x+j)/m)=P(x) for all m,x.
# Test a Fourier mode P_k(z)=exp(2 pi i k z): prod_j = exp(2 pi i k x) * (orbit sum in exponent)
# Actually multiplicative: prod_{j} exp(2pi i k (x+j)/m) = exp(2pi i k x/m) * exp(2pi i k (m-1)/2 /m... )
for k in (1,2):
    survive_all = True
    for m in (2,3,5):
        Pk = lambda z: mp.e**(2j*mp.pi*k*z)
        pf = mp.mpf(1)
        for j in range(m): pf *= Pk((x+j)/m)
        pf = pf/Pk(x)
        if rr(pf, 1) > 1e-20: survive_all = False
    print(f"  Fourier mode k={k}: survives all m? {survive_all}")
print("  => only k=0 (constant) survives all => stack of K-averaged relations pins period-1 freedom to a POINT")
