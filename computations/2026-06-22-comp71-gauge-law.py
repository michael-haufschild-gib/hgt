"""comp71 [P1] / gpt/proof9 verification — the canonical zero-free gauge law.

proof9 Lemma 3:  Xi -> e^{q(w^2)} Xi,  q(w^2)=sum_{r>=1} a_r w^{2r}
                 ==>  T_k -> T_k + 2k(-1)^{k+1} a_k     (DIAGONAL in k).
Canonical fix:   T_k^can = T_k^raw - 2k(-1)^{k+1} a_k.
Hankel counterterm:  (Dq H^0)_{ij} = 2(i+j+1)(-1)^{i+j+2} a_{i+j+1}.

comp68 verified ONLY k=1 (T_1 -> T_1 + 2c).  Here: verify the closed form at
k=1..6 (sign pattern + 2k factor), DIAGONALITY (multi-term q), the Hankel
counterterm, and canonical recovery.  Mechanism check: T_k = 2(-1)^{k+1} k c_{2k}
with c_{2k}=[w^{2k}]logXi, and logXi -> logXi + q(w^2) shifts c_{2k} -> c_{2k}+a_k.
We extract c_{2k} from BOTH the analytic-pieces formula AND an independent
mp.taylor of logXi to anchor the law to the actual Xi (not one formula)."""
import mpmath as mp
mp.mp.dps = 80
K = 6

# ---- canonical c_{2k} = [w^{2k}] log Xi(w), three analytic pieces (T_moments_exact internals)
def c_pieces(kmax):
    M = 2*kmax+1
    a = [mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m) for m in range(M+1)]   # zeta Taylor at 1/2
    g = [mp.mpf(0)]*(M+1); g[0] = mp.log(a[0])                              # log of that series
    for m in range(1,M+1):
        s = mp.fsum(n*g[n]*a[m-n] for n in range(1,m))
        g[m] = (m*a[m]-s)/(m*a[0])
    c = [None]*(kmax+1)
    for k in range(1,kmax+1):
        c[k] = (-mp.power(4,k)/k                                            # log(1-4w^2) piece
                + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k))  # logGamma(1/4+w/2)
                + g[2*k])                                                    # log zeta(1/2+w)
    return c   # c[k] = c_{2k}

c = c_pieces(K)
def T_from_c(c):  # proof9/T_moments_exact:  T_k = 2(-1)^{k+1} k c_{2k}
    return [None]+[2*((-1)**(k+1))*k*c[k] for k in range(1,K+1)]
T_can = T_from_c(c)

# ---- INDEPENDENT anchor: c_{2k} via mp.taylor of the ACTUAL log Xi(w)
def logXi(w):
    s = mp.mpf('0.5')+w
    return mp.log(mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s))
tay = mp.taylor(logXi, 0, 2*K+1)            # numerical Taylor of the real logXi
c_anchor = [None]+[tay[2*k] for k in range(1,K+1)]
anchor_err = max(abs(c_anchor[k]-c[k]) for k in range(1,K+1))
print("logXi-Taylor vs analytic-pieces c_{2k}: max abs diff =", mp.nstr(anchor_err,3))
print("T_1 (canonical) =", mp.nstr(T_can[1],12), "  T_2 =", mp.nstr(T_can[2],12))

# ---- predicted gauge shift (proof9)
def dT(k,a): return 2*k*((-1)**(k+1))*a[k]      # 2k(-1)^{k+1} a_k

# ===== TEST A: multi-term gauge, all orders nonzero (rationals) -> diagonal closed form
aA = [None, mp.mpf(3)/7, -mp.mpf(5)/11, mp.mpf(2)/13, -mp.mpf(1)/17, mp.mpf(7)/19, -mp.mpf(4)/23]
c_g = [None]+[c[k]+aA[k] for k in range(1,K+1)]   # gauge: c_{2k} -> c_{2k}+a_k
T_raw = T_from_c(c_g)
print("\n=== TEST A: multi-term gauge q=sum a_r w^{2r}, a_r all nonzero ===")
print(" k   T_raw - T_can           proof9 2k(-1)^{k+1}a_k      abs error")
maxerrA = mp.mpf(0)
for k in range(1,K+1):
    lhs = T_raw[k]-T_can[k]; rhs = dT(k,aA); e=abs(lhs-rhs); maxerrA=max(maxerrA,e)
    print(f" {k}  {mp.nstr(lhs,16):>22}  {mp.nstr(rhs,16):>22}  {mp.nstr(e,3)}")
print("TEST A max abs error =", mp.nstr(maxerrA,3))

# ===== TEST B: DIAGONALITY — gauge ONLY a_3 nonzero, confirm ONLY T_3 moves
print("\n=== TEST B: diagonality (only a_3 != 0) -> only T_3 shifts ===")
aB = [None]+[mp.mpf(0)]*K; aB[3] = mp.mpf('0.37')
c_g = [None]+[c[k]+aB[k] for k in range(1,K+1)]; T_raw = T_from_c(c_g)
for k in range(1,K+1):
    shift = T_raw[k]-T_can[k]
    print(f" T_{k} shift = {mp.nstr(shift,12):>16}   (expect {'2*3*(+1)*0.37=2.22' if k==3 else '0'})")

# ===== TEST C: Hankel counterterm on H^0_{ij}=T_{i+j+1}
print("\n=== TEST C: Hankel counterterm (Dq H^0)_{ij}=2(i+j+1)(-1)^{i+j+2}a_{i+j+1} ===")
d = 2                                   # need T up to 2d+1 = 5
def H0(T): return mp.matrix([[T[i+j+1] for j in range(d+1)] for i in range(d+1)])
c_g = [None]+[c[k]+aA[k] for k in range(1,K+1)]; T_raw = T_from_c(c_g)
H_can, H_raw = H0(T_can), H0(T_raw)
maxerrC = mp.mpf(0)
for i in range(d+1):
    for j in range(d+1):
        n=i+j+1; pred=2*n*((-1)**(i+j+2))*aA[n]
        e=abs((H_raw[i,j]-H_can[i,j])-pred); maxerrC=max(maxerrC,e)
print("TEST C max abs error (matrix vs Hankel counterterm) =", mp.nstr(maxerrC,3))

# ===== TEST D: canonical recovery T_k^can = T_raw - 2k(-1)^{k+1}a_k == T_can
c_g = [None]+[c[k]+aA[k] for k in range(1,K+1)]; T_raw = T_from_c(c_g)
maxerrD = max(abs((T_raw[k]-dT(k,aA))-T_can[k]) for k in range(1,K+1))
print("\n=== TEST D: canonical recovery T_k^can == T_k ===")
print("TEST D max abs error =", mp.nstr(maxerrD,3))

print("\nSUMMARY:", "ALL PASS" if max(maxerrA,maxerrC,maxerrD,anchor_err)<mp.mpf(10)**(-60) else "CHECK FAILURES")
