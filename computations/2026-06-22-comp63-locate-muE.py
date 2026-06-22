"""comp63 / rt#63: locate/characterize the signed seam measure mu_E.
E = R^P_x - J (protector basis x=y+0.16); E_{ij}=e_{i+j} (Hankel symbol, comp56). Extract e_n
from the OFF-tridiagonal entries (verify Hankel consistency), then analyze:
 - support: |e_n|^{1/n}, e_{n+1}/e_n  (dominant point of mu_E in x);  x=0 <-> y=-0.16 boundary pt
 - sign pattern (mu_E signed); inertia of the FULL Hankel [e_{i+j}]
 - F_E(z)=sum e_n z^n: radius of convergence -> nearest singularity (support edge in x)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
y0=mp.mpf('-0.16')
def shiftS(d):
    S=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(i+1): S[j,i]=mp.binomial(i,j)*mp.power(-y0,i-j)
    return S
for d in [12,18]:
    mp.mp.dps=int(7*d)+130
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); RP=A-B
    S=shiftS(d); RPx=S.T*RP*S
    # off-tridiagonal Hankel symbol: for each antidiag n=i+j, take an off-trid entry (|i-j|>=2)
    e={}; hank_ok=mp.mpf(0)
    for n in range(2,2*d-1):
        vals=[(i,RPx[i,n-i]) for i in range(max(0,n-d),min(d,n)+1) if 0<=n-i<=d and abs(2*i-n)>=2]
        if vals:
            e[n]=vals[len(vals)//2][1]
            if len(vals)>1:
                mn=mp.fsum(v for _,v in vals)/len(vals)
                hank_ok=max(hank_ok, max(abs(v-mn)/abs(mn) for _,v in vals if mn!=0))
    ns=sorted(e); 
    print(f"d={d}: Hankel consistency of e_n (max antidiag deviation) = {mp.nstr(hank_ok,2)}")
    # ratios and roots
    print(f"  e_n sample (n, e_n, sign): " + " ".join(f"{n}:{'+' if e[n]>0 else '-'}{float(mp.log10(abs(e[n]))):.1f}" for n in ns[:8]))
    rat=[float(e[ns[k+1]]/e[ns[k]]) for k in range(len(ns)-1)]
    print(f"  e_{{n+1}}/e_n (dominant x-point): first={rat[0]:.4f} ... last few={[round(r,4) for r in rat[-4:]]}")
    rootn=[float(abs(e[n])**(mp.mpf(1)/n)) for n in ns]
    print(f"  |e_n|^(1/n) (1/radius): first={rootn[0]:.4f} ... last={rootn[-1]:.4f}  -> support edge |x|~{1/rootn[-1] if rootn[-1]>0 else float('inf'):.4f}")
    # sign changes
    sc=sum(1 for k in range(len(ns)-1) if e[ns[k]]*e[ns[k+1]]<0)
    print(f"  sign changes in e_n: {sc}/{len(ns)-1}")
    if d==18:
        # full Hankel inertia of [e_{i+j}] (use available n=2..; build a Hankel block we have)
        nlo=ns[0]; sz=(len(ns)+1)//2
        Hk=mp.matrix(sz,sz)
        ok=True
        for i in range(sz):
            for j in range(sz):
                idx=nlo+i+j
                if idx in e: Hk[i,j]=e[idx]
                else: ok=False
        if ok:
            ev=mp.eigsy((Hk+Hk.T)/2,eigvals_only=True); npos=sum(1 for x in ev if x>0); nneg=sum(1 for x in ev if x<0)
            print(f"  full-Hankel [e_{{i+j}}] block ({sz}x{sz}) inertia=({npos},{nneg})  -> mu_E is {'POSITIVE' if nneg==0 else 'SIGNED'} measure")
