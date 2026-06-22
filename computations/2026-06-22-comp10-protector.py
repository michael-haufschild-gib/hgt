"""comp10 / rt#36: is the trivial-zero protector concentrated at j=1, or spread?
On the dangerous mode p_d (lambda_min eigvec of (H^0,M_triv)), decompose the protector mass
M_triv[p_d]=sum_{j>=1}(2j+1/2)^{-2} p_d(y_j)^2, y_j=-(2j+1/2)^{-2}. Report the fraction at
j=1, cum j<=2, j<=5, and the smallest J reaching 99%. Track vs d. Also where the THREAT
(zero side Q_0[p_d]=2 sum_n y_n p_d(y_n)^2) concentrates (peak on-line atom n*)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
DPS=int(sys.argv[1]); DS=[int(x) for x in sys.argv[2].split(',')]
gammas=H.load_zeros('zeros.txt', max(DS)+60)
def yj(j): return -mp.power(2*j+mp.mpf('0.5'),-2)
def wj(j): return mp.power(2*j+mp.mpf('0.5'),-2)
for d in DS:
    mp.mp.dps=DPS
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    Lc=mp.cholesky(B); Li=mp.inverse(Lc); C=Li*A*Li.T; C=(C+C.T)/2
    E,Q=mp.eigsy(C); idx=min(range(len(E)),key=lambda i:E[i])
    q=mp.matrix([Q[r,idx] for r in range(d+1)]); c=Li.T*q   # dangerous poly coeffs
    pol=lambda y: mp.fsum(c[i]*mp.power(y,i) for i in range(d+1))
    # protector decomposition
    terms=[(j, wj(j)*pol(yj(j))**2) for j in range(1,400)]
    tot=mp.fsum(t for _,t in terms)
    frac1=terms[0][1]/tot
    cum=mp.mpf(0); cum2=cum5=None; J99=None
    for j,t in terms:
        cum+=t
        if j==2: cum2=cum/tot
        if j==5: cum5=cum/tot
        if J99 is None and cum/tot>mp.mpf('0.99'): J99=j
    # threat side concentration: peak on-line atom
    znat=[(n+1, 2*(1/(gammas[n]**2))*pol(1/(gammas[n]**2))**2) for n in range(min(len(gammas),3*d+40))]
    nstar=max(znat,key=lambda z:abs(z[1]))[0]
    ovu=H.overlap_with_pole(c)
    print(f"d={d:2d}: protector frac j=1={mp.nstr(frac1,5)}  cum j<=2={mp.nstr(cum2,5)}  j<=5={mp.nstr(cum5,5)}  J(99%)={J99}  | threat peak n*={nstar} (gamma~{mp.nstr(gammas[nstar-1],4)})  overlap_u={mp.nstr(ovu,5)}",flush=True)
