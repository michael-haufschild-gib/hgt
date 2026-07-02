"""Grid design feasibility: (a) rational-s obstructed points near modulus 3, arg in [156,180];
(b) one square-tree certificate with rounded rational data re-verified rigorously."""
import numpy as np
from fractions import Fraction as F

# ---------- (a) rational-s trick: b = (1-s^2)/4, P1 condition |s-3|^2 |s+1|^2 <= 16 exactly ----------
print("=== rational-s obstructed candidates (P1) ===")
targets = [156.5, 160, 165, 170, 175, 180]
for deg in targets:
    b_t = 3*np.exp(1j*np.radians(deg))
    s_t = np.sqrt(1-4*b_t)
    s_t = s_t if s_t.real >= 0 else -s_t
    # round to denominator 16
    for den in (16, 32):
        u = F(round(s_t.real*den), den); v = F(round(s_t.imag*den), den)
        # exact rational arithmetic
        s2 = (u*u - v*v, 2*u*v)                       # s^2 = (re, im)
        bre = (1 - s2[0])/4; bim = -s2[1]/4
        n1 = (u-3)**2 + v*v                            # |s-3|^2
        n2 = (u+1)**2 + v*v                            # |s+1|^2
        cond = n1*n2 <= 16
        mod2 = bre*bre + bim*bim
        if cond and F(17,4) < mod2 < 10:
            print(f"  deg~{deg}: s = {u} + {v}i  -> b = {bre} + {bim}i ; |s-3|^2|s+1|^2 = {float(n1*n2):.3f} <= 16 OK ; |b|^2 = {float(mod2):.4f} ; arg(b) = {np.degrees(np.arctan2(float(bim),float(bre))):.2f} deg")
            break
    else:
        print(f"  deg~{deg}: no den<=32 candidate")

# ---------- (b) rounded-rational square-tree certificate, rigorous re-verification ----------
print("\n=== rounded certificate feasibility at modulus~3, 150 deg ===")
def xstar(B): return (1.0+np.sqrt(1.0+4.0*B))/2.0
# Gaussian-rational b near 3 e^{i 150deg}: b = -2.598+1.5i ~ (-13/5, 3/2)
bre, bim = F(-13,5), F(3,2)
b = complex(bre, bim)
print(f"b = {bre} + {bim}i, |b| = {abs(b):.4f}, arg = {np.degrees(np.angle(b)):.2f} deg")

# emit tree with float chains, then re-verify each leaf with rational-rounded chain data
def chain_data(c0, r0, maxd=60):
    xs = xstar(abs(b))*1.0005
    c, r = c0, r0; out=[]
    for d in range(maxd):
        r = r*(2*abs(c)+r); c = c*c+b
        out.append((c, r))
        if abs(c)-r > xs: return out
        if r > abs(c)+xs: return None
    return None

leaves=[]; stack=[(F(0),F(0),F(1))]
while stack:
    cx,cy,h = stack.pop()
    dx = max(abs(cx)-h, 0); dy = max(abs(cy)-h, 0)
    if dx*dx+dy*dy > 1: continue
    cd = chain_data(complex(cx,cy), float(h)*np.sqrt(2))
    if cd is not None:
        leaves.append(((cx,cy,h), len(cd)))
        continue
    h2 = h/2
    for sx in (-h2,h2):
        for sy in (-h2,h2): stack.append((cx+sx,cy+sy,h2))

print(f"leaves: {len(leaves)}, max chain depth: {max(l[1] for l in leaves)}")

# rigorous rational re-verification of one leaf chain with rounded data (denominator 10^6)
import math
def rup(x, den=10**6):   return F(math.ceil(x*den), den)    # upper bound rounding
def rdown(x, den=10**6): return F(math.floor(x*den), den)   # lower bound rounding
def rround(x, den=10**6): return F(round(x*den), den)
(cx,cy,h), _ = leaves[len(leaves)//2]
# rational chain: c_i rational (rounded), containment slack checked in EXACT rationals
c_exact = (cx, cy)
r_i = None
# initial: disk D((cx,cy), h*sqrt2): use rational r0 with r0^2 >= 2h^2
r0 = rup(float(h)*np.sqrt(2)*1.0000001)
assert r0*r0 >= 2*h*h
ci = (cx, cy); ri = r0; ok=True; steps=0
while True:
    steps += 1
    # exact image center: ci^2 + b
    ecx = ci[0]*ci[0] - ci[1]*ci[1] + bre
    ecy = 2*ci[0]*ci[1] + bim
    # rounded next center
    ncx, ncy = rround(float(ecx)), rround(float(ecy))
    # Ni >= |ci| rational: Ni^2 >= |ci|^2
    Ni = rup(np.sqrt(float(ci[0]**2+ci[1]**2))*1.000001)
    assert Ni*Ni >= ci[0]**2+ci[1]**2
    # drift = |exact - rounded| bound: D^2 >= (ecx-ncx)^2+(ecy-ncy)^2
    Dr = rup(np.sqrt(float((ecx-ncx)**2+(ecy-ncy)**2))*1.01+1e-9)
    assert Dr*Dr >= (ecx-ncx)**2+(ecy-ncy)**2
    nri = ri*(2*Ni+ri) + Dr
    ci, ri = (ncx,ncy), nri
    # escape check: lower bound M <= |ci|: M^2 <= |ci|^2 ; need M - ri > xstar upper bound X
    M = rdown(np.sqrt(float(ci[0]**2+ci[1]**2))*0.999999)
    if M*M <= ci[0]**2+ci[1]**2:
        # X >= xstar(|b|): S^2 >= 1+4*Nb, Nb^2 >= |b|^2, X = (1+S)/2
        Nb = rup(abs(b)*1.000001); assert Nb*Nb >= bre*bre+bim*bim
        S = rup(np.sqrt(1+4*float(Nb))*1.000001); assert S*S >= 1+4*Nb
        X = (1+S)/2
        if M - ri > X:
            print(f"leaf chain rationally certified in {steps} steps; digits of last numerator ~ {len(str(ci[0].numerator))}")
            break
    if steps > 20:
        ok=False; print("leaf failed rational recheck"); break
