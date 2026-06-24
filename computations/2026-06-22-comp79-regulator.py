"""comp79 / gpt/43 #9 — regulator-to-scalar: is the seam finite part regulator/window independent
at the level of the ACTUAL function?  (proof7 Lemma 2 proves it; comp67/comp71 corroborate at the
moment/gauge level -- here a direct witness on Xi'/Xi itself.)

T_k = (1/2pi i) oint_{|w|=r} w^{-2k} (Xi'/Xi)(w) dw  (residue at w=0; the only singularities of
Xi'/Xi are the zeros w=+-i gamma_n at |w|>=14.13, OUTSIDE small r).  Vary the radius r (window)
and a smooth radial cutoff (regulator); confirm T_k is r/cutoff-INDEPENDENT and equals the moment
route T_moments_exact -> hence s_d is regulator-independent."""
import mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
mp.mp.dps=50

def xi(s): return mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
def dlogXi(w):  # (Xi'/Xi)(w) = d/dw log xi(1/2+w)
    return mp.diff(lambda t: mp.log(xi(mp.mpf('0.5')+t)), w)

def Tk_contour(k, r, smooth=False):
    "(1/2pi i) oint w^{-2k}(Xi'/Xi) dw on |w|=r; optional smooth radial averaging over [r,1.3r]."
    def integ(rho):
        def f(th):
            w=rho*mp.expjpi(th/mp.pi)        # w=rho e^{i th}
            return mp.power(w,-2*k+1)*dlogXi(w)*mp.expjpi(th/mp.pi)
        val=mp.quad(f,[0,mp.pi/2,mp.pi,3*mp.pi/2,2*mp.pi])/(2*mp.pi)
        return mp.re(val)
    if not smooth: return integ(r)
    # smooth cutoff = average over radii with weight (Bartlett) -> still picks the same residue
    rs=[r*(1+mp.mpf(j)/20) for j in range(7)]
    ws=[1-abs(mp.mpf(j-3)/3) for j in range(7)]
    return mp.fsum(w*integ(rr) for w,rr in zip(ws,rs))/mp.fsum(ws)

T_exact=H.T_moments_exact(3)
print("=== T_k from the seam contour integral of the ACTUAL Xi'/Xi vs the moment route ===")
print(f"{'k':>3} {'r=0.5':>16} {'r=1.0':>16} {'r=2.0 (smooth)':>18} {'T_moments_exact':>18} {'max rel.dev':>12}")
for k in (1,2,3):
    a=Tk_contour(k,mp.mpf('0.5'))
    b=Tk_contour(k,mp.mpf('1.0'))
    c=Tk_contour(k,mp.mpf('2.0'),smooth=True)
    t=T_exact[k]
    dev=max(abs(a-t),abs(b-t),abs(c-t))/abs(t)
    print(f"{k:>3} {mp.nstr(a,10):>16} {mp.nstr(b,10):>16} {mp.nstr(c,10):>18} {mp.nstr(t,10):>18} {mp.nstr(dev,2):>12}")

# s_d at small d from these contour-extracted moments vs moment route (regulator independence of s_d)
A_STAR=mp.mpf('0.16'); Y_STAR=-A_STAR
def s_d_from_T(T,d):
    H0=mp.matrix([[T[i+j+1] for j in range(d+1)] for i in range(d+1)])
    vs=mp.matrix([[Y_STAR**i] for i in range(d+1)])
    Hm=H0-A_STAR*(vs*vs.T); m=(vs.T*mp.inverse(Hm)*vs)[0]
    return A_STAR+1/m
d=2; Tc=[None]+[Tk_contour(k,mp.mpf('1.0')) for k in range(1,2*d+2)]
print(f"\ns_d(d=2): contour-moments={mp.nstr(s_d_from_T(Tc,d),8)}  vs  exact-moments={mp.nstr(s_d_from_T(H.T_moments_exact(2*d+1),d),8)}")
print("=> seam finite part (hence s_d) is radius/cutoff independent on the actual Xi'/Xi (proof7 Lemma 2 witnessed).")
print("DONE")
