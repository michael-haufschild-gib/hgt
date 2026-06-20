# Does |R(s)|=1 hold ONLY on sigma=1/2?  R(s)=Gamma_R(s)/Gamma_R(1-s), Gamma_R(s)=pi^{-s/2}Gamma(s/2).
# Delta(sigma,t) = log|R| = log|Gamma_R(sigma+it)| - log|Gamma_R(1-sigma+it)|  (odd about 1/2, zero at 1/2).
# Check: is Delta nonzero for sigma != 1/2, for a range of t (incl. large)?  And is |Gamma_R(sigma+it)| monotone in sigma?
import mpmath as mp
mp.mp.dps = 30
def logGammaR_abs(s): return mp.re(-(s/2)*mp.log(mp.pi) + mp.loggamma(s/2))  # log|Gamma_R(s)|
def Delta(sig,t):
    s=mp.mpf(sig)+1j*mp.mpf(t)
    return logGammaR_abs(s) - logGammaR_abs(1-s)
print("Delta(sigma,t) for sigma in (0.5,1], scan for off-line zeros / sign changes:")
for t in [1,10,50,100,300,1000,5000]:
    vals=[]
    sigs=[mp.mpf(k)/40 for k in range(20,41)]  # 0.5 .. 1.0
    for sig in sigs:
        vals.append(Delta(sig,t))
    # monotone increasing on (0.5,1]? and sign always >=0?
    diffs=[float(vals[i+1]-vals[i]) for i in range(len(vals)-1)]
    mono = all(d>0 for d in diffs)
    signpos = all(float(v)>=-1e-25 for v in vals)
    minval=min(float(v) for v in vals[1:])  # exclude sigma=0.5 (=0)
    print(f"  t={t:6}: Delta strictly incr on (.5,1]={mono}, all>=0={signpos}, min Delta on (.5,1]={minval:+.4e}, Delta(1,t)={float(vals[-1]):+.5f}")
# Also: derivative of g(sigma)=log|Gamma_R| in sigma = -1/2 log pi + 1/2 Re psi((sigma+it)/2); check sign near sigma=1/2 for large t
print("\n g'(sigma)= -1/2 log pi + 1/2 Re psi((sigma+it)/2) at sigma=0.5:")
for t in [1,50,1000,5000]:
    gp = -0.5*mp.log(mp.pi) + 0.5*mp.re(mp.digamma((mp.mpf('0.5')+1j*t)/2))
    print(f"  t={t:6}: g'(0.5)={float(gp):+.5f}  (sign of how |Gamma_R| moves at the line)")
