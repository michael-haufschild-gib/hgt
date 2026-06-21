"""
Analytical step: is the single negative direction of Q_arch the pole direction u_i=(-4)^i, and does
Q_prime cancel it there (the s=1 entireness), leaving the RH content on the codim-1 complement?

S_k^A leading = 2^{2k}=4^k ⟹ T^A_k=(-1)^k S_k^A has leading (-4)^k ⟹ [T^A_{i+j+1}] ≈ -4·u u*, u_i=(-4)^i
(rank-1 NEGATIVE). Claim: (i) the negative eigenvector of Q_arch ≈ u; (ii) Q_arch[u]<0, Q_prime[u]>0 of
matching ~4^... scale, Q_0[u]=Q_arch[u]+Q_prime[u] small (pole cancellation = entireness); (iii) Q_arch
restricted to u^perp is PD (the d positive directions). Verify all three.
"""
import sys, mpmath as mp
KMAX_d = int(sys.argv[1]) if len(sys.argv) > 1 else 6      # DMAX
mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 80
d = KMAX_d; ORD = 2*(2*d+1)
def A(w): return 1/(mp.mpf(1)/2+w)+1/(w-mp.mpf(1)/2)-mp.log(mp.pi)/2+mp.digamma((mp.mpf(1)/2+w)/2)/2
def P(w): return mp.zeta(mp.mpf(1)/2+w,1,1)/mp.zeta(mp.mpf(1)/2+w)
ca = mp.taylor(A,0,ORD); cp = mp.taylor(P,0,ORD)
SA = {k:-ca[2*k-1] for k in range(1,2*d+2)}; SP = {k:-cp[2*d-0] if False else -cp[2*k-1] for k in range(1,2*d+2)}
def Hk(S,n):
    H=mp.matrix(n+1,n+1)
    for i in range(n+1):
        for j in range(n+1): H[i,j]=(-1)**(i+j+1)*S[i+j+1]
    return H
HA=Hk(SA,d); HP=Hk(SP,d); H0=Hk({k:SA[k]+SP[k] for k in SA},d)
def form(H,c): return mp.fsum(c[i]*c[j]*H[i,j] for i in range(d+1) for j in range(d+1))
u=[mp.mpf(-4)**i for i in range(d+1)]
# normalize u
nu=mp.sqrt(mp.fsum(x**2 for x in u)); un=[x/nu for x in u]
EA,VA=mp.eigsy(HA)
negvec=[VA[i,0] for i in range(d+1)]     # eigenvector of most-negative eigenvalue of HA
# overlap of negvec with u (abs cosine)
ov=abs(mp.fsum(negvec[i]*un[i] for i in range(d+1)))
print(f"# pole-direction test, d={d}, dps={mp.mp.dps}")
print(f"# (i) Q_arch most-negative eigenvalue = {mp.nstr(EA[0],5)}; |<negeigvec, u_hat>| = {mp.nstr(ov,8)}  (->1 means it IS the pole dir)")
print(f"# (ii) on u=(-4)^i:  Q_arch[u]={mp.nstr(form(HA,u),6)}  Q_prime[u]={mp.nstr(form(HP,u),6)}  Q_0[u]={mp.nstr(form(H0,u),6)}")
print(f"#      ratio |Q_0[u]| / |Q_arch[u]| = {mp.nstr(abs(form(H0,u)/form(HA,u)),4)}  (small = pole cancels)")
# (iii) Q_arch on u^perp: project out u, check remaining inertia is all positive
EApos=sum(1 for e in EA if e>0); EAneg=sum(1 for e in EA if e<0)
print(f"# (iii) Q_arch inertia (npos,nneg)=({EApos},{EAneg}); Q_0 inertia=({sum(1 for e in mp.eigsy(H0,eigvals_only=True) if e>0)},{sum(1 for e in mp.eigsy(H0,eigvals_only=True) if e<0)})")
