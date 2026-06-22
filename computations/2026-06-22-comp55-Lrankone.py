"""comp55 / rt#55 / gpt39 c3: does the rank-one boundary theorem generalize to Dirichlet L?
For each real primitive chi: coarsest trivial-zero image y_*=-(a+1/2)^{-2}, mass a_*=(a+1/2)^{-2}=|y_*|
(even a=0: y_*=-4,a_*=4; odd a=1: y_*=-4/9,a_*=4/9). Test H^0_chi=H^-_chi+a_* v_* v_*^T with
inertia(H^-_chi)=(d,1), and the unified scalar gap s=1/(v_*^T(H^0)^{-1}v_*)=a_*+1/(v_*^T(H^-)^{-1}v_*)
=a_**margin. If (d,1) holds for all chi => rank-one boundary theorem is completed-Euler-product-general."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py")
def ev(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
def genmin(A,B):
    Li=mp.inverse(mp.cholesky(B)); C=Li*A*Li.T; return min(mp.eigsy((C+C.T)/2,eigvals_only=True))
def inertia(M):
    E=mp.eigsy((M+M.T)/2,eigvals_only=True); return sum(1 for e in E if e>0),sum(1 for e in E if e<0)
for name in ['zeta','chi4','chi3','chi5','chi8']:
    for d in [8,12]:
        mp.mp.dps=int(7*d)+130
        if name=='zeta':
            a=2; T=H.T_moments_exact(2*d+1); B=H.Mtriv_matrix(d)   # zeta protector starts j>=1 (effective a-shift b=5/4); y_*=-0.16
            ystar=mp.mpf('-0.16'); astar=mp.power(mp.mpf('2.5'),-2)
        else:
            a=L.CHARS[name][1]; T=L.T_moments_L(name,2*d+1); B=L.Mtriv_L_matrix(d,a)
            astar=mp.power(mp.mpf(a)+mp.mpf('0.5'),-2); ystar=-astar
        A=H.H0_matrix(d,T); v=ev(ystar,d)
        Hm=A-astar*(v*v.T)
        ip,inn=inertia(Hm)
        Mi=mp.inverse(Hm); m=(v.T*Mi*v)[0]; s_schur=astar+1/m
        s_chris=1/(v.T*mp.inverse(A)*v)[0]
        s_marg=astar*genmin(A,B)
        ok="(d,1)" if (ip==d and inn==1) else f"({ip},{inn})!"
        if d==12 or True:
            print(f"{name:5s} d={d:2d} a={a}: y_*={mp.nstr(ystar,5)} a_*={mp.nstr(astar,4)}  inertia(H^-)={ok}  "
                  f"s(Schur)={mp.nstr(s_schur,5)} =1/K? {mp.nstr(abs(s_schur-s_chris)/abs(s_chris),2)}  =a_**margin? {mp.nstr(abs(s_schur-s_marg)/abs(s_marg),2)}",flush=True)
