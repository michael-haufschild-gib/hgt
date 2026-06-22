"""comp65 (rt#65): generalized-Nevanlinna N1 test. m_sigma(z)=Cauchy transform of
sigma=nu'-a_* delta_{y_*} = 2 sum_n y_n/(y_n-z) - a_*/(y_*-z). Pick matrix
P_ij=(m(z_i)-conj m(z_j))/(z_i-conj z_j) on samples z_i in C^+ ; count negative eigenvalues
(=kappa). Expect 1 (the boundary-atom negative-residue pole). Then inject an off-line quartet
into nu' and recount.
comp70 (rt#70): m_d(y)=v(y)^T (H^-_d)^{-1} v(y) (poly deg 2d); real roots interlacing/convergence
across d (finite sections of one boundary triple?)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
a_=mp.power(mp.mpf('2.5'),-2); ystar=mp.mpf('-0.16')
print("=== comp65: N1 Pick test (count negative squares of m_sigma) ===")
mp.mp.dps=60
g=H.load_zeros('zeros400.txt',80); yn=[1/(x*x) for x in g]
zs=[mp.mpc('0.3','0.5'),mp.mpc('-0.5','0.4'),mp.mpc('0.1','1.2'),mp.mpc('-2.0','0.3'),
    mp.mpc('0.05','0.2'),mp.mpc('-0.16','0.6'),mp.mpc('1.0','0.8'),mp.mpc('-1.0','1.5'),
    mp.mpc('0.2','0.05'),mp.mpc('-0.3','0.9')]
def msig(z, extra=None):
    s=2*mp.fsum(y/(y-z) for y in yn) - a_/(ystar-z)
    if extra:
        for (yc,wt) in extra: s+=wt/(yc-z)
    return s
def pick_negs(extra=None):
    n=len(zs); P=mp.zeros(n,n)
    for i in range(n):
        for j in range(n):
            P[i,j]=(msig(zs[i],extra)-mp.conj(msig(zs[j],extra)))/(zs[i]-mp.conj(zs[j]))
    P=(P+P.T.conjugate())/2
    ev=mp.eigh(P, eigvals_only=True)
    return sum(1 for e in ev if e<-mp.mpf('1e-20')*max(abs(x) for x in ev))
print(f"  actual zeros (RH): kappa = {pick_negs()}  (expect 1 = boundary atom)")
# inject off-line quartet at gamma0=20, beta-1/2=0.1 : w=+-d+-i g0, y=-1/w^2, weight 2y per atom
d_=mp.mpf('0.1'); g0=mp.mpf('20')
ws=[mp.mpc(d_,g0),mp.mpc(-d_,g0),mp.mpc(d_,-g0),mp.mpc(-d_,-g0)]
extra=[(-1/(w*w), 2*(-1/(w*w))) for w in ws]
print(f"  with off-line quartet (g0=20,delta=0.1): kappa = {pick_negs(extra)}")
print("=== comp70: m_d(y) roots interlacing across d ===")
def ev(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
prevroots=None
for d in [6,8,10]:
    mp.mp.dps=int(7*d)+120
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); v=ev(ystar,d); Hm=A-a_*(v*v.T); Hi=mp.inverse(Hm)
    # m_d(y)=sum_{ij} y^{i+j} Hi[i,j] -> poly coeffs c_k = sum_{i+j=k} Hi[i,j]
    cf=[mp.mpf(0)]*(2*d+1)
    for i in range(d+1):
        for j in range(d+1): cf[i+j]+=Hi[i,j]
    roots=mp.polyroots(list(reversed(cf)), maxsteps=200, extraprec=200)
    realr=sorted([mp.re(r) for r in roots if abs(mp.im(r))<mp.mpf('1e-20')*abs(r) or abs(mp.im(r))<1e-30])
    print(f"  d={d}: {len(realr)} real roots of m_d(y); sample (exterior, y<0): {[mp.nstr(r,5) for r in realr if r<0][:5]}")
    prevroots=realr
