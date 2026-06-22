"""comp69 / rt#69 / gpt42-4: compare the Hankel-tail profile across zeta/real-L/DH.
For each, build H^0 (own moments), M_triv (own Gamma protector), R^P=H^0-M_triv, shift to the
Gamma-selected protector point x=y-y_*, tridiagonal split, tail Hankel symbol e_n. Report the
dominant x-point e_{n+1}/e_n (predicted = y_1+|y_*|, i.e. lowest zero) and sign-change count.
GENUINELY UNKNOWN: does DH's tail match the genuine-L pattern (zero-dominated) or deviate BEFORE
the d=62 gap crossing?"""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py"); hb=imp("hb","2026-06-22-hurwitz-batch.py")
d=14; DPS=int(7*d)+150; mp.mp.dps=DPS
def DH_moments(kmax):
    q=5; chi={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}; chibar={r:mp.conj(v) for r,v in chi.items()}
    kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1); M=2*kmax; half=mp.mpf('0.5'); lq=mp.log(q)
    hco={r: hb.hurwitz_taylor(mp.mpf(r)/q, half, M) for r in range(1,q)}
    e=[mp.power(q,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
    def Lt(cm):
        out=[mp.mpc(0)]*(M+1)
        for r in range(1,q):
            c=cm[r]; h=hco[r]
            for m in range(M+1): out[m]=out[m]+c*mp.fsum(e[j]*h[m-j] for j in range(m+1))
        return out
    ax=Lt(chi); axb=Lt(chibar); af=[mp.re(((1-1j*kk)/2)*ax[m]+((1+1j*kk)/2)*axb[m]) for m in range(M+1)]
    g=[mp.mpf(0)]*(M+1); g[0]=mp.log(af[0])
    for m in range(1,M+1):
        s=mp.fsum(n*g[n]*af[m-n] for n in range(1,m)); g[m]=(m*af[m]-s)/(m*af[0])
    b=mp.mpf(3)/4; cn=lambda n: mp.polygamma(n-1,b)/(mp.factorial(n)*mp.power(2,n))+g[n]
    return [None]+[2*((-1)**(k+1))*k*cn(2*k) for k in range(1,kmax+1)]
def find_g1(name):
    if name=='zeta': return H.load_zeros('zeros400.txt',1)[0]
    mp.mp.dps=40
    if name=='DH':
        q=5; chi={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}; chibar={r:mp.conj(v) for r,v in chi.items()}
        kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
        Lc=lambda s,cm: mp.power(q,-s)*mp.fsum(cm[r]*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q))
        Z=lambda t: mp.re(((1-1j*kk)/2)*Lc(mp.mpf('0.5')+1j*t,chi)+((1+1j*kk)/2)*Lc(mp.mpf('0.5')+1j*t,chibar))
    else:
        Z=lambda t: mp.re(L.xi_chi(name, mp.mpf('0.5')+1j*t))
    t=mp.mpf('0.2'); vp=Z(t)
    while t<40:
        t+=mp.mpf('0.1'); v=Z(t)
        if vp==0 or v*vp<0: 
            g=mp.findroot(Z,t-mp.mpf('0.05')); 
            if g>0.1: mp.mp.dps=DPS; return g
        vp=v
    mp.mp.dps=DPS; return None
def profile(name):
    mp.mp.dps=DPS
    if name=='zeta': T=H.T_moments_exact(2*d+1); B=H.Mtriv_matrix(d); a=2; ystar=mp.mpf('-0.16')
    elif name=='DH': T=DH_moments(2*d+1); a=1; B=L.Mtriv_L_matrix(d,a); ystar=-mp.power(mp.mpf('1.5'),-2)
    else: a=L.CHARS[name][1]; T=L.T_moments_L(name,2*d+1); B=L.Mtriv_L_matrix(d,a); ystar=-mp.power(mp.mpf(a)+mp.mpf('0.5'),-2)
    A=H.H0_matrix(d,T); RP=A-B
    S=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(i+1): S[j,i]=mp.binomial(i,j)*mp.power(-ystar,i-j)
    RPx=S.T*RP*S
    e={}
    for n in range(2,2*d-1):
        vals=[RPx[i,n-i] for i in range(max(0,n-d),min(d,n)+1) if 0<=n-i<=d and abs(2*i-n)>=2]
        if vals: e[n]=vals[len(vals)//2]
    ns=sorted(e); rat=float(e[ns[-1]]/e[ns[-2]]); sc=sum(1 for k in range(len(ns)-1) if e[ns[k]]*e[ns[k+1]]<0)
    g1=find_g1(name); y1=1/(g1*g1) if g1 else None
    pred=float(y1-ystar) if y1 else None
    return ystar,rat,pred,sc,len(ns),g1
print(f"# tail profile (d={d}): dominant x-point e_{{n+1}}/e_n vs predicted y_1+|y_*| (lowest zero), sign-changes")
for nm in ['zeta','chi4','chi5','DH']:
    ystar,rat,pred,sc,nn,g1=profile(nm)
    match = "MATCH(zero-dominated)" if pred and abs(rat-pred)/abs(pred)<0.05 else "DEVIATES"
    print(f"  {nm:5s}: y_*={float(ystar):+.4f} gamma_1={float(g1):.3f}  dominant e_n+1/e_n={rat:.5f}  pred(y_1+|y_*|)={pred:.5f}  -> {match}  sign-changes={sc}/{nn-1}",flush=True)
