"""comp56 / rt#56 / gpt39 c5: what IS the tail E? In protector basis R^P_x=S^T R^P S (S: y->y+0.16),
J=tridiagonal part, E=R^P_x-J. Test E's algebraic form (NOT its norm):
 (a) Hankel? E_{ij}=f(i+j)   (b) Toeplitz? E_{ij}=g(i-j)
 (c) displacement rank of E (rank of E - Z E Z^T, Z=down-shift)  (d) inertia/rank-split (E=AA*-BB*)."""
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
def numrank(M,tol):
    E=mp.eigsy((M+M.T)/2,eigvals_only=True) if M.rows==M.cols else None
    sv=sorted([abs(x) for x in (E if E else [])],reverse=True)
    return sum(1 for x in sv if x>tol*max(sv)) if sv else None
for d in [10,14]:
    mp.mp.dps=int(6.5*d)+110
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); RP=A-B
    S=shiftS(d); RPx=S.T*RP*S
    J=mp.zeros(d+1,d+1); E=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1):
            (J if abs(i-j)<=1 else E)[i,j]=RPx[i,j]
    fr=lambda M:mp.sqrt(mp.fsum(M[i,j]**2 for i in range(d+1) for j in range(d+1)))
    # (a) Hankel test: for each s=i+j, deviation of E_{ij} across the antidiagonal
    hdev=mp.mpf(0); hn=mp.mpf(0)
    for ss in range(d+1, 2*d+1):  # off-tridiag antidiagonals only meaningful; sample all
        vals=[E[i,ss-i] for i in range(max(0,ss-d),min(d,ss)+1) if abs(2*i-ss)>1]
        if len(vals)>1:
            mn=mp.fsum(vals)/len(vals); hdev+=mp.fsum((x-mn)**2 for x in vals); hn+=mp.fsum(x**2 for x in vals)
    hankel=mp.sqrt(hdev/hn) if hn>0 else mp.mpf('nan')
    # (b) Toeplitz test: deviation along diagonals i-j=const
    tdev=mp.mpf(0); tn=mp.mpf(0)
    for dd in range(2,d+1):
        vals=[E[i,i-dd] for i in range(dd,d+1)]+[E[i-dd,i] for i in range(dd,d+1)]
        vals=[x for x in vals if x!=0]
        if len(vals)>1:
            mn=mp.fsum(vals)/len(vals); tdev+=mp.fsum((x-mn)**2 for x in vals); tn+=mp.fsum(x**2 for x in vals)
    toep=mp.sqrt(tdev/tn) if tn>0 else mp.mpf('nan')
    # (c) displacement rank: D = E - Z E Z^T (Z down-shift)
    Z=mp.zeros(d+1,d+1)
    for i in range(1,d+1): Z[i,i-1]=1
    Dz=E-Z*E*Z.T
    dr=numrank(Dz,mp.mpf('1e-25'))
    # (d) E inertia (rank split)
    Ee=mp.eigsy((E+E.T)/2,eigvals_only=True); npos=sum(1 for x in Ee if x>1e-30*fr(E)); nneg=sum(1 for x in Ee if x<-1e-30*fr(E))
    print(f"d={d}: ||E||/||R^P_x||={mp.nstr(fr(E)/fr(RPx),3)}  Hankel-dev={mp.nstr(hankel,3)}  Toeplitz-dev={mp.nstr(toep,3)}  displ-rank(E-ZEZ^T)={dr}  inertia(E)=({npos},{nneg})",flush=True)
