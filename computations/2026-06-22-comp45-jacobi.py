"""comp45 / rt#45 / gpt38-c1: protector-point Jacobi model R^P = J + E.
R^P=H^0-M_triv in the SHIFT basis phi_i=(y+0.16)^i (comp14: 99.994% tridiagonal there).
J = tridiagonal part, E = rest. Report ||E||/||R^P||, inertia(J)/inertia(E)/inertia(R^P),
Jacobi coeffs (diag a_i, offdiag b_i) and their pattern, and SIGN-ESSENTIALITY of E:
does J-only preserve margin = lambda_min(H^0,M_triv)>0, or does dropping E flip it?"""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
y0=mp.mpf('-0.16')   # protector point; shift x = y - y0 = y + 0.16
def shiftS(d):  # phi_i=(y-y0)^i in monomial coords: S[j,i]=C(i,j)(-y0)^{i-j}
    S=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(i+1): S[j,i]=mp.binomial(i,j)*mp.power(-y0,i-j)
    return S
def inertia(M):
    E=mp.eigsy((M+M.T)/2,eigvals_only=True)
    return sum(1 for e in E if e>0),sum(1 for e in E if e<0)
def frob(M): return mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows) for j in range(M.cols)))
def genmin(A,B):
    Li=mp.inverse(mp.cholesky(B)); C=Li*A*Li.T; return min(mp.eigsy((C+C.T)/2,eigvals_only=True))
for d in [8,12,16]:
    mp.mp.dps=int(6.5*d)+110
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); RP=A-B
    S=shiftS(d); Si=mp.inverse(S); RPx=S.T*RP*S
    J=mp.zeros(d+1,d+1); E=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1):
            if abs(i-j)<=1: J[i,j]=RPx[i,j]
            else: E[i,j]=RPx[i,j]
    relE=frob(E)/frob(RPx)
    ipR,inR=inertia(RP); ipJ,inJ=inertia(J); ipE,inE=inertia(E)
    margin=genmin(A,B)
    # sign-essentiality: map J back to monomial, rebuild H^0_J=M_triv + S^{-T} J S^{-1}
    RPJ=Si.T*J*Si; AJ=B+RPJ; marginJ=genmin(AJ,B)
    diag=[mp.nstr(J[i,i],4) for i in range(d+1)]
    off =[mp.nstr(J[i,i+1],4) for i in range(d)]
    print(f"d={d}: ||E||/||R^P||={mp.nstr(relE,3)}  inertia R^P=({ipR},{inR}) J=({ipJ},{inJ}) E=({ipE},{inE})")
    print(f"     margin(full)={mp.nstr(margin,4)}  margin(J-only)={mp.nstr(marginJ,4)}  -> E sign-essential: {'YES (J flips/destroys sign)' if marginJ<=0 or abs(mp.log10(abs(marginJ/margin)))>2 else 'no (J preserves)'}",flush=True)
    if d==12:
        print(f"     J diag a_i = {diag}")
        print(f"     J offdiag b_i = {off}")
