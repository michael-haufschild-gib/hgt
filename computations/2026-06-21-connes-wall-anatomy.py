"""
Combined Q_0-wall anatomy, sharing one expensive setup (cached zeros + T_k + A/P Taylor split).
Loads /root/gam_cache.txt (precompute-zeros.py) so each mode runs in seconds.

Coordinate: y=-(rho-1/2)^{-2}; H0=[T_{i+j+1}] is the Q_0 wall (zero-sum). Weld Xi'/Xi=A+P splits
H0=HA(arch,Gamma-only)+HP(prime,zeta'/zeta). u_i=(-4)^i = eval at the cancelled s=1 pole (y=-4),
<c,u>=p(-4).

modes:
  resid   - rank-one pole structure + residual positivity on u^perp (gpt/29 1-4): the central test.
  danger  - arch/prime anatomy on H0's lambda_min direction p_d (gpt/28 1,3): who protects positivity.
  offline - push atom m off line, locate the new negative direction vs u and vs p_d (gpt/28 5).
  band    - per-atom contribution profile of p_d: top/mid/tail multiscale split (gpt/28 4).
args: mode N DMAX dps  [m for offline]
"""
import sys, mpmath as mp
mode=sys.argv[1] if len(sys.argv)>1 else "resid"
N   =int(sys.argv[2]) if len(sys.argv)>2 else 200
DMAX=int(sys.argv[3]) if len(sys.argv)>3 else 6
mp.mp.dps=int(sys.argv[4]) if len(sys.argv)>4 else 120
KMAX=2*DMAX+1; ORD=2*KMAX+2

# --- load cached zeros ---
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    p=2*k-1; return (1/mp.pi)*TN**(-p)/p*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/p)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
# Archimedean S_k^A in CLOSED FORM (no Taylor of zeta'/zeta -> no hang).
# A(w)=1/(1/2+w)+1/(w-1/2)-log(pi)/2+psi((1/2+w)/2)/2; SA_k=-[w^{2k-1}]A.
#   poles: -[w^{2k-1}](1/(1/2+w)+1/(w-1/2)) = 2^{2k}+2^{2k}=2^{2k+1}
#   psi:   [w^{2k-1}](psi((1/2+w)/2)/2) = polygamma(2k-1,1/4)/(2^{2k}(2k-1)!)
def SA_poly(k): return 2**(2*k+1)-mp.polygamma(2*k-1,mp.mpf(1)/4)/(2**(2*k)*mp.factorial(2*k-1))
SA={k:SA_poly(k) for k in range(1,KMAX+1)}
# prime part is then FREE: T_k=(-1)^k(SA_k+SP_k) => SP_k=(-1)^k T_k - SA_k, and HP=H0-HA.
SP={k:(-1)**k*T[k]-SA[k] for k in range(1,KMAX+1)}
# cross-check SA against fast Taylor of A (digamma only, no zeta'/zeta -> no hang)
def Awf(w): return 1/(mp.mpf(1)/2+w)+1/(w-mp.mpf(1)/2)-mp.log(mp.pi)/2+mp.digamma((mp.mpf(1)/2+w)/2)/2
_ca=mp.taylor(Awf,0,2*KMAX+1)
_xc=max(abs(SA_poly(k)-(-_ca[2*k-1]))/abs(SA_poly(k)) for k in (1,2,KMAX))
print(f"# SA cross-check (polygamma vs Taylor[A]) max rel err = {mp.nstr(_xc,3)}")

def Hk(get,n):
    H=mp.matrix(n+1,n+1)
    for i in range(n+1):
        for j in range(n+1): H[i,j]=get(i+j+1)
    return H
def inertia(H):
    E=mp.eigsy(H,eigvals_only=True); return sum(1 for e in E if e>0),sum(1 for e in E if e<0),min(E),max(E)
def form(H,c): return mp.fsum(c[i]*c[j]*H[i,j] for i in range(H.rows) for j in range(H.cols))
def uvec(d):
    u=[mp.mpf(-4)**i for i in range(d+1)]; nu=mp.sqrt(mp.fsum(x*x for x in u)); return u,[x/nu for x in u]
def gram_perp(u):
    n=len(u); nu=mp.sqrt(mp.fsum(x*x for x in u)); basis=[[x/nu for x in u]]
    for e in range(n):
        v=[mp.mpf(1) if i==e else mp.mpf(0) for i in range(n)]
        for b in basis:
            dp=mp.fsum(b[i]*v[i] for i in range(n)); v=[v[i]-dp*b[i] for i in range(n)]
        nv=mp.sqrt(mp.fsum(x*x for x in v))
        if nv>mp.mpf(10)**(-mp.mp.dps//2): basis.append([x/nv for x in v])
        if len(basis)==n: break
    return basis[1:]
def restrict(H,B):
    m=len(B); R=mp.matrix(m,m)
    for a in range(m):
        for b in range(m):
            R[a,b]=mp.fsum(B[a][i]*H[i,j]*B[b][j] for i in range(H.rows) for j in range(H.cols))
    return R

print(f"# mode={mode} N={N} DMAX={DMAX} dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")

if mode=="resid":
    for d in range(2,DMAX+1):
        H0=Hk(lambda k:T[k],d); HA=Hk(lambda k:(-1)**k*SA[k],d); HP=Hk(lambda k:(-1)**k*SP[k],d)
        _,VA=mp.eigsy(HA); negv=[VA[i,0] for i in range(d+1)]
        u,uh=uvec(d); ov=abs(mp.fsum(negv[i]*uh[i] for i in range(d+1)))
        pA,nA,_,_=inertia(HA)
        B=gram_perp(u); HAp=restrict(HA,B); H0p=restrict(H0,B)
        pAp,nAp,minAp,_=inertia(HAp); p0p,n0p,min0p,_=inertia(H0p)
        E0=mp.eigsy(H0,eigvals_only=True); cond0=abs(max(E0))/abs(min(E0))
        E0p=mp.eigsy(H0p,eigvals_only=True); cond0p=abs(max(E0p))/abs(min(E0p))
        Qa=form(HA,u); Qp=form(HP,u); Q0=form(H0,u)
        print(f"d={d}: inertia(HA)=({pA},{nA}) |<negHA,u>|={mp.nstr(ov,7)}")
        print(f"      HA|u^perp=({pAp},{nAp}) min={mp.nstr(minAp,4)}  H0|u^perp=({p0p},{n0p}) min={mp.nstr(min0p,4)}")
        print(f"      cond(H0)={mp.nstr(cond0,4)} cond(H0|u^perp)={mp.nstr(cond0p,4)} improve x{mp.nstr(cond0/cond0p,4)}")
        print(f"      on u: Qa={mp.nstr(Qa,5)} Qp={mp.nstr(Qp,5)} Q0={mp.nstr(Q0,5)} depth={mp.nstr(abs(Q0/Qa),4)}")

elif mode=="danger":
    for d in range(2,DMAX+1):
        H0=Hk(lambda k:T[k],d); HA=Hk(lambda k:(-1)**k*SA[k],d); HP=Hk(lambda k:(-1)**k*SP[k],d)
        E,V=mp.eigsy(H0); pd=[V[i,0] for i in range(d+1)]
        u,uh=uvec(d); npd=mp.sqrt(mp.fsum(x*x for x in pd)); pdh=[x/npd for x in pd]
        ovu=abs(mp.fsum(pdh[i]*uh[i] for i in range(d+1)))
        Qa=form(HA,pd); Qp=form(HP,pd); Q0=form(H0,pd)
        verdict="ARCH-DOMINATION" if (Qa>0 and abs(Qa)>=abs(Qp)) else "PRIME-DELICATE"
        print(f"d={d}: lmin={mp.nstr(E[0],5)} |<p_d,u>|={mp.nstr(ovu,6)} Qa={mp.nstr(Qa,5)} Qp={mp.nstr(Qp,5)} Q0={mp.nstr(Q0,5)} |Qa|/|Qp|={mp.nstr(abs(Qa)/abs(Qp),5)} -> {verdict}")

elif mode=="offline":
    d=DMAX; m=int(sys.argv[5]) if len(sys.argv)>5 else 1
    H0=Hk(lambda k:T[k],d); _,V0=mp.eigsy(H0); pd=[V0[i,0] for i in range(d+1)]
    npd=mp.sqrt(mp.fsum(x*x for x in pd)); pdh=[x/npd for x in pd]
    u,uh=uvec(d); g=gam[m-1]
    print(f"# push atom m={m} (gamma={mp.nstr(g,6)})")
    for beta in [mp.mpf('0'),mp.mpf('0.05'),mp.mpf('0.1'),mp.mpf('0.2'),mp.mpf('0.4')]:
        w=mp.mpc(beta,g); yo=-1/w**2; yb=mp.conj(yo)
        def Tk(k): return T[k]-2*(mp.mpf(1)/g**2)**k+2*(yo**k+yb**k)
        Hp=Hk(lambda k:mp.re(Tk(k)),d); E,V=mp.eigsy(Hp); vneg=[V[i,0] for i in range(d+1)]
        ovu=abs(mp.fsum(vneg[i]*uh[i] for i in range(d+1)))
        ovp=abs(mp.fsum(vneg[i]*pdh[i] for i in range(d+1)))
        npos=sum(1 for e in E if e>0); nneg=sum(1 for e in E if e<0)
        print(f"beta={mp.nstr(beta,3)}: lmin={mp.nstr(E[0],5)} inertia=({npos},{nneg}) |<neg,u>|={mp.nstr(ovu,5)} |<neg,p_d>|={mp.nstr(ovp,5)}")

elif mode=="band":
    d=DMAX; H0=Hk(lambda k:T[k],d); E,V=mp.eigsy(H0); pd=[V[i,0] for i in range(d+1)]
    y=[mp.mpf(1)/g**2 for g in gam]
    def pv(yy): return mp.fsum(pd[i]*yy**i for i in range(d+1))
    c=[2*y[n]*pv(y[n])**2 for n in range(N)]; tot=mp.fsum(c); fr=[ci/tot for ci in c]
    peak=max(range(N),key=lambda n:c[n]); cum=mp.mpf(0); n50=n90=None
    for n in range(N):
        cum+=fr[n]
        if n50 is None and cum>=0.5: n50=n+1
        if n90 is None and cum>=0.9: n90=n+1; break
    top=mp.fsum(c[n] for n in range(min(3,N)))/tot
    mid=mp.fsum(c[n] for n in range(3,min(20,N)))/tot
    tl =mp.fsum(c[n] for n in range(min(20,N),N))/tot
    print(f"# lmin=Q0[p_d]={mp.nstr(E[0],6)} sum_c={mp.nstr(tot,6)} peak n*={peak+1}(gamma={mp.nstr(gam[peak],5)},frac={mp.nstr(fr[peak],4)})")
    print(f"# 50% within n<={n50}; 90% within n<={n90}; top(1-3)={mp.nstr(top,4)} mid(4-20)={mp.nstr(mid,4)} tail(>=21)={mp.nstr(tl,4)}")
    print(f"# first 8 fr: "+" ".join(mp.nstr(fr[n],3) for n in range(min(8,N))))
