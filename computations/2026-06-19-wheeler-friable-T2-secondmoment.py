from mpmath import mp, mpf, log, exp, factorial, digamma, polygamma, zeta, pslq, fac, nsum, inf
mp.dps = 60

S = [2,3]
def friable_list(Nmax):
    out=[]
    a=0
    while 2**a <= Nmax:
        b=0
        while 2**a * 3**b <= Nmax:
            out.append(2**a*3**b); b+=1
        a+=1
    return sorted(out)

# --- ZS and derivatives from the analytic product (independent of hand ZS'/ZS forms) ---
def zS(s):
    p=mpf(1)
    for q in S: p*= 1/(1-mpf(q)**(-s))
    return p
def zS_d(s,k):
    # k-th derivative of zS at s via mpmath diff
    from mpmath import diff
    return diff(lambda t: zS(t), s, k)

gE = -digamma(1)   # Euler gamma
print("gE check:", gE)

# Basis B (11 monomials)
L2=log(2); L3=log(3); z2=zeta(2)
B = [mpf(1), gE, gE**2, z2, L2, L3, L2**2, L3**2, L2*L3, gE*L2, gE*L3]
Bnames=["1","gE","gE^2","z2","log2","log3","log2^2","log3^2","log2log3","gE*log2","gE*log3"]

def H(j):    return sum(mpf(1)/k for k in range(1,j+1))
def H2(j):   return sum(mpf(1)/k**2 for k in range(1,j+1))

Nmax = 3**13   # plenty: smallest power n^-(j+1), j>=0 converges fast
fl = friable_list(Nmax)
print("friable terms:", len(fl), "max", fl[-1])

print("\n j |  Lclosed - Ldirect (should be ~0)  |  M_j^(2) - predicted (should be ~0)")
for j in range(0,7):
    jf = factorial(j)
    Hj=H(j); H2j=H2(j)
    # closed form L_j^(2) = j![ zS(j+1)*((Hj-gE)^2 + z2 - H2j) + 2*zS'(j+1)*(Hj-gE) + zS''(j+1) ]
    z0=zS(j+1); z1=zS_d(j+1,1); z2d=zS_d(j+1,2)
    Lclosed = jf*( z0*((Hj-gE)**2 + z2 - H2j) + 2*z1*(Hj-gE) + z2d )
    # direct friable sum using mpmath digamma/polygamma (fully independent)
    psi=digamma(j+1); psi1=polygamma(1,j+1)
    G0=jf; G1=jf*psi; G2=jf*(psi**2+psi1)   # Gamma, Gamma', Gamma'' at j+1
    Ldirect=mpf(0)
    for n in fl:
        ln=log(n)
        Ldirect += mpf(n)**(-(j+1))*( G2 - 2*ln*G1 + ln**2*G0 )
    # M_j^(2)
    Mj = Lclosed/(jf*z0)
    # predicted coefficient vector over B
    r2 = -1/(mpf(2)**(j+1)-1); r3 = -1/(mpf(3)**(j+1)-1)
    s2 = mpf(2)**(j+1)/(mpf(2)**(j+1)-1)**2; s3 = mpf(3)**(j+1)/(mpf(3)**(j+1)-1)**2
    pred = {
      "1": Hj**2 - H2j, "gE": -2*Hj, "gE^2": mpf(1), "z2": mpf(1),
      "log2": 2*Hj*r2, "log3": 2*Hj*r3,
      "log2^2": s2 + r2**2, "log3^2": s3 + r3**2, "log2log3": 2*r2*r3,
      "gE*log2": -2*r2, "gE*log3": -2*r3 }
    Mpred = sum(pred[nm]*B[i] for i,nm in enumerate(Bnames))
    print(f"{j:2d} | {mp.nstr(Lclosed-Ldirect,5):>14} | {mp.nstr(Mj-Mpred,5):>14}")

# --- PSLQ discovery on j=0,1: confirm B is complete (no missing monomial) ---
print("\nPSLQ discovery (find M_j^(2) as integer relation w/ basis, then it's exact rational):")
for j in [0,1,2]:
    jf=factorial(j); Hj=H(j); H2j=H2(j); z0=zS(j+1); z1=zS_d(j+1,1); z2d=zS_d(j+1,2)
    Mj = ( z0*((Hj-gE)**2 + z2 - H2j) + 2*z1*(Hj-gE) + z2d )
    vec = [Mj] + B
    rel = pslq(vec, maxcoeff=10**8, maxsteps=10**5)
    print(f" j={j}: pslq([M_j^(2)]+B) =", rel)
