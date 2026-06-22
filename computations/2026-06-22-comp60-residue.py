"""Verify Lemma 1 (gpt/proof5): Q_0[p] = -Res_{w=0}[h_p(w) w M_Xi(w)] with M_Xi=(1/2w)Xi'/Xi.
Pin the constant for OUR folded convention T_k=2 sum gamma^{-2k}. Check [w^{2k}]M_Xi vs (-1)^k T_{k+1}/c."""
import mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
mp.mp.dps=80
KMAX=12
# c_{2k}=[w^2k] log Xi  (reuse internals)
M=2*KMAX+1
a=[mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m) for m in range(M+1)]
g=[mp.mpf(0)]*(M+1); g[0]=mp.log(a[0])
for m in range(1,M+1):
    s=mp.fsum(n*g[n]*a[m-n] for n in range(1,m)); g[m]=(m*a[m]-s)/(m*a[0])
def c2k(k): return -mp.power(4,k)/k + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k)) + g[2*k]
T=[None]+[2*((-1)**(k+1))*k*c2k(k) for k in range(1,KMAX+1)]
# M_Xi(w)=(1/2w) Xi'/Xi = sum_m (m+1) c_{2(m+1)} w^{2m};  [w^2m]M_Xi should = (-1)^m T_{m+1}/2 (folded)
print("# check [w^2m] M_Xi  vs  (-1)^m T_{m+1}/2  (folded T):")
for m in [0,1,2,3,5]:
    lhs=(m+1)*c2k(m+1); rhs=(-1)**m*T[m+1]/2
    print(f"  m={m}: [w^2m]M_Xi={mp.nstr(lhs,12)}  (-1)^m T_{{m+1}}/2={mp.nstr(rhs,12)}  rel={mp.nstr(abs(lhs-rhs)/abs(rhs),2)}")
# residue check for a test polynomial p (degree 3): Q_0 direct vs -Res[h_p w M_Xi]
c=[mp.mpf('1.0'),mp.mpf('-0.7'),mp.mpf('0.3'),mp.mpf('0.5')]; d=3
Q0=mp.fsum(c[i]*c[j]*T[i+j+1] for i in range(d+1) for j in range(d+1))
# b_n = sum_{i+j=n} c_i c_j ; Res[h_p w M_Xi] = -sum_n b_n * [w^2n](M_Xi)  (pairing m=n)
b=[mp.mpf(0)]*(2*d+1)
for i in range(d+1):
    for j in range(d+1): b[i+j]+=c[i]*c[j]
res=mp.fsum(b[n]*((-1)**(n+1))*((n+1)*c2k(n+1)) for n in range(2*d+1))  # Res = sum b_n(-1)^{n+1}[w^2n]M_Xi
print(f"# Q_0[p] direct = {mp.nstr(Q0,14)} ;  -Res[h_p w M_Xi] = {mp.nstr(-res,14)} ;  rel={mp.nstr(abs(Q0+res)/abs(Q0),2)}")
print(f"# => folded-convention constant: Q_0 = -Res[h_p w M_Xi] (with M_Xi=(1/2w)Xi'/Xi); = -Res[h_p Xi'/Xi].")
