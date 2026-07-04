#!/usr/bin/env python3
"""(EFF-M4/M10) exact moment ladder + Chernoff for ReP_X, X = T^(1/5), T = 3e12.
Exact single-cosine cumulants via Fraction power series of log J0;
totals via power sums S_j = sum p^-2j... ; moments via cumulant recursion;
Chernoff exact-model ceiling via prod I0; truncation-honesty for the
certified (degree<=10) version. Lean on memory."""
from fractions import Fraction as F
import math
import numpy as np

# --- J0 series coefficients: J0(x) = sum (-1)^m x^{2m}/(4^m (m!)^2), to x^12
M = 7
j0c = [F((-1)**m, 4**m * math.factorial(m)**2) for m in range(M)]  # coeff of x^{2m}

# --- log series: log(1+u), u = J0-1 as series in y=x^2 up to y^6
def mul(a, b, n):
    c = [F(0)]*n
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if i+j < n: c[i+j] += ai*bj
    return c
n = M  # y-degree cutoff (y = x^2)
u = [F(0)] + j0c[1:]           # u(y): starts at y^1
L = [F(0)]*n                   # log J0 as series in y
upow = [F(1)] + [F(0)]*(n-1)   # u^0
for k in range(1, n):
    upow = mul(upow, u, n)
    sgn = F((-1)**(k+1), k)
    for i in range(n): L[i] += sgn*upow[i]
# characteristic fn: log J0(v) = sum_j L[j] v^{2j}; cumulants kappa_{2j}:
# log E e^{ivX} = sum (-1)^j kappa_{2j} v^{2j}/(2j)!  =>  kappa_{2j} = (-1)^j L[j] (2j)!
kap_cos = {2*j: (-1)**j * L[j] * math.factorial(2*j) for j in range(1, n)}
print("single-cos cumulants:", {k: str(v) for k, v in kap_cos.items()})

# --- primes and power sums
T = 3e12; X = T**0.2
def primes_upto(nn):
    s = list(range(nn+1)); s[0]=s[1]=0
    for i in range(2, int(nn**0.5)+1):
        if s[i]:
            for j in range(i*i, nn+1, i): s[j] = 0
    return [p for p in s if p]
P = primes_upto(int(X))
S = {j: sum(1.0/p**j for p in P) for j in range(1, n)}
print(f"#primes={len(P)}  X={X:.1f}  S1={S[1]:.6f} S2={S[2]:.6f} S3={S[3]:.6f}")
# total cumulants of ReP: kappa_{2j}(ReP) = kap_cos[2j]*S_j   (a_p^{2j} = p^{-j})
K = {2*j: float(kap_cos[2*j])*S[j] for j in range(1, n)}
print("total cumulants:", {k: f"{v:.6f}" for k, v in K.items()})

# --- moments from cumulants: m_n = sum_{k} C(n-1,k-1) kappa_k m_{n-k} (kappa odd = 0)
mom = {0: 1.0}
for nn in range(1, 13):
    tot = 0.0
    for k in range(2, nn+1, 2):
        if k in K:
            tot += math.comb(nn-1, k-1)*K[k]*mom[nn-k]
    mom[nn] = tot
s1 = S[1]; sg2 = s1/2
gauss = {2: sg2, 4: 3*sg2**2, 6: 15*sg2**3, 8: 105*sg2**4, 10: 945*sg2**5, 12: 10395*sg2**6}
for nn in (2, 4, 6, 8, 10, 12):
    print(f"m{nn} EXACT = {mom[nn]:.4f}   Gauss {gauss[nn]:.2f}   ratio {mom[nn]/gauss[nn]:.3f}")
print("m4 closed-form check:", 0.75*s1**2 - 0.375*S[2])

# --- Chernoff ceiling (exact independent model): min_v e^{-va} prod I0(v/sqrt p)
amps = np.array([1.0/math.sqrt(p) for p in P])
def chern(a):
    vs = np.linspace(0.05, 20, 8000)
    lg = -vs*a + np.array([np.log(np.i0(amps*v)).sum() for v in vs])
    i = int(lg.argmin())
    return math.exp(lg[i]), float(vs[i])
for a in (3.1, 4.1, 5.1, 6.1):
    b, vst = chern(a)
    print(f"Chernoff-exact P(ReP<=-{a}) <= {b:.3e}   v*={vst:.2f}")

# --- certified ladder: Markov with exact moments (t-transfer error ~1e-3 rel, MV-spacing)
print("\ncertified Markov (exact moments, + MV-spacing rel err ~1e-3):")
for aP in (3.6, 4.1, 4.6, 5.1):
    row = "  aP=%.1f: " % aP
    for nn in (6, 8, 10, 12):
        row += f"m{nn}: {mom[nn]/aP**nn:.2e}  "
    print(row)

# --- truncated-Chernoff honesty: remainder of e^{-vX} beyond degree J, |X|<=B
B = amps.sum()
print(f"\nsupport bound B = {B:.3f}")
for v in (0.8, 1.0, 1.2, 1.5, 2.0):
    for J in (10, 12):
        # remainder <= sum_{j>J} v^j E|X|^j / j!  with E|X|^j <= mom[J]*B^{j-J} (j>J even-ish)
        rem = sum(v**j * mom[J]*B**(j-J)/math.factorial(j) for j in range(J+1, 40))
        print(f"  v={v} J={J}: exp-truncation remainder <= {rem:.2e}")
