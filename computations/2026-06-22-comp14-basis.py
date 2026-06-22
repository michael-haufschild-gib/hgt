"""comp14 / rt#42: is R^P=H^0-M_triv simplifiable in some basis? Inertia is Sylvester-invariant
(confirm corpus (1,4)/(2,5)/(2,7)); bandedness is basis-dependent. Report off-tridiagonal energy
fraction in: monomial, mu_triv-orthonormal (S=L^{-T}), shift-to-(-0.16) (exterior Christoffel pt),
shift-to-(-4) (pole). If any basis bands/decays R^P => new operator route; if none => 'global
inequality or nothing'."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def inertia(Msym):
    E=mp.eigsy(Msym,eigvals_only=True)
    npos=sum(1 for e in E if e>0); nneg=sum(1 for e in E if e<0)
    return npos,nneg,min(E),max(E)
def offband(M):  # fraction of Frobenius energy with |i-j|>1
    n=M.rows; tot=mp.fsum(M[i,j]**2 for i in range(n) for j in range(n))
    off=mp.fsum(M[i,j]**2 for i in range(n) for j in range(n) if abs(i-j)>1)
    return mp.sqrt(off/tot)
def shiftS(d,y0):  # columns: (y-y0)^i expanded in monomial y^j => S[j,i]=C(i,j)(-y0)^{i-j}
    S=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(i+1):
            S[j,i]=mp.binomial(i,j)*mp.power(-y0,i-j)
    return S
for d in [6,8,10]:
    mp.mp.dps=max(120,int(6.5*d)+90)
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    RP=A-B
    ip,inn,mn,mx=inertia((RP+RP.T)/2)
    # bases
    L=mp.cholesky(B); LiT=mp.inverse(L).T   # mu_triv-orthonormal: S=L^{-T}
    bands={}
    bands['monomial']=offband(RP)
    bands['mutriv-ON']=offband(LiT.T*RP*LiT)
    S16=shiftS(d,mp.mpf('-0.16')); bands['shift(-0.16)']=offband(S16.T*RP*S16)
    S4 =shiftS(d,mp.mpf('-4'));    bands['shift(-4)pole']=offband(S4.T*RP*S4)
    bs=" ".join(f"{k}={mp.nstr(v,3)}" for k,v in bands.items())
    print(f"d={d:2d}: inertia R^P=({ip},{inn}) min={mp.nstr(mn,4)} max={mp.nstr(mx,3)} | offband-energy: {bs}",flush=True)
