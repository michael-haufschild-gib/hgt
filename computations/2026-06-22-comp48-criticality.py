"""comp48 / rt#48 / gpt38-c4: is the first trivial zero a HARD boundary datum?
Remove the j=1 protector atom: H0_minus = H^0 - (2.5)^{-2} e(-0.16)e(-0.16)^T.
Then the modified protector dominates iff H0_minus + a*e(y_*)e(y_*)^T >= 0; the critical
mass is a_c(y_*) = -1/(e(y_*)^T H0_minus^{-1} e(y_*)). Scan y_*<0: does y_*=-0.16 MINIMIZE
a_c (optimal protector point), and is a_c(-0.16) ~ the true mass 0.16? If yes => boundary-Weyl
hard datum; if broad slack => single-point story weakens."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def evec(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
for d in [8,12,16]:
    mp.mp.dps=int(6.5*d)+120
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    e0=evec(mp.mpf('-0.16'),d); w1=mp.power(mp.mpf('2.5'),-2)   # j=1 weight 0.16
    Hm=A-w1*(e0*e0.T); Hm=(Hm+Hm.T)/2
    En=mp.eigsy(Hm,eigvals_only=True); ipn=sum(1 for x in En if x>0); inn=sum(1 for x in En if x<0)
    Hmi=mp.inverse(Hm)
    def ac(y):
        q=(evec(y,d).T*Hmi*evec(y,d))[0]
        return -1/q if q<0 else mp.mpf('inf')   # need q<0 (restoration) for finite positive mass
    # scan y_* over exterior negative grid; find minimizer
    grid=[mp.mpf(g)/100 for g in range(-500,0,2)]   # -5.00 .. -0.02
    vals=[(y,ac(y)) for y in grid]
    fin=[(y,a) for y,a in vals if a!=mp.mpf('inf') and a>0]
    ymin,amin=min(fin,key=lambda t:t[1]) if fin else (None,None)
    ac016=ac(mp.mpf('-0.16'))
    margin=min(mp.eigsy((mp.inverse(mp.cholesky(B))*A*mp.inverse(mp.cholesky(B)).T),eigvals_only=True))
    print(f"d={d}: inertia(H0_minus)=({ipn},{inn}); a_c(-0.16)={mp.nstr(ac016,8)} (true mass 0.16, deficit={mp.nstr(mp.mpf('0.16')-ac016,3)}); "
          f"argmin a_c at y*={mp.nstr(ymin,5)} a_c={mp.nstr(amin,8)}  [margin={mp.nstr(margin,3)}]",flush=True)
