"""Batched Hurwitz-zeta Taylor coefficients: ALL derivatives in ONE Euler-Maclaurin sweep.
h[n] = zeta^{(n)}(s0,a)/n!  for n=0..M.  Solves the DH moment-build cost (mpmath redoes a full
sweep per derivative order; this does one sweep for all orders)."""
import mpmath as mp
def hurwitz_taylor(a, s0, M, N=None, J=None):
    if N is None: N=int(mp.mp.dps*1.2)+M+10
    if J is None: J=int(mp.mp.dps*0.6)+5
    a=mp.mpf(a); s0=mp.mpf(s0)
    h=[mp.mpf(0)]*(M+1)
    # main sum  sum_{k=0}^{N-1} (k+a)^{-s} ; coeff of u^n is (k+a)^{-s0} (-log)^n / n!
    for k in range(N):
        g=k+a; p=mp.power(g,-s0); L=mp.log(g); t=p
        for n in range(M+1):
            h[n]+=t; t*=-L/(n+1)
    g=N+a; L=mp.log(g); gh=mp.power(g,mp.mpf('0.5')-s0+mp.mpf('0.5'))  # placeholder
    # tail term1: g^{1-s}/(s-1), s=s0+u.  = g^{1-s0} e^{-uL} / (u+(s0-1))
    g1=mp.power(g,1-s0); c=s0-1
    ek=[mp.power(-L,m)/mp.factorial(m) for m in range(M+1)]       # e^{-uL}
    inv=[ -mp.power(-1/c,k+1) for k in range(M+1)]                # 1/(u+c)=sum (-1)^k u^k / c^{k+1}? = (1/c) sum (-u/c)^k
    inv=[ mp.power(-1,k)/mp.power(c,k+1) for k in range(M+1)]
    for n in range(M+1):
        h[n]+= g1*mp.fsum(ek[m]*inv[n-m] for m in range(n+1))
    # tail term2: (1/2) g^{-s}
    g0=mp.power(g,-s0)
    for n in range(M+1): h[n]+= mp.mpf('0.5')*g0*ek[n]
    # tail term3: sum_j B_{2j}/(2j)! (s)_{2j-1} g^{-s-(2j-1)} ; (s)_{2j-1}=prod_{i=0}^{2j-2}(s0+u+i)
    for j in range(1,J+1):
        Bf=mp.bernoulli(2*j)/mp.factorial(2*j)
        # poly in u: prod_{i=0}^{2j-2} (s0+i + u)
        poly=[mp.mpf(1)]
        for i in range(2*j-1):
            r=s0+i; poly=[ (poly[t-1] if t>0 else mp.mpf(0)) + (r*poly[t] if t<len(poly) else mp.mpf(0)) for t in range(len(poly)+1)]
        gpow=mp.power(g,-s0-(2*j-1)); ekp=[gpow*mp.power(-L,m)/mp.factorial(m) for m in range(M+1)]
        deg=len(poly)-1
        for n in range(M+1):
            h[n]+= Bf*mp.fsum(poly[t]*ekp[n-t] for t in range(min(deg,n)+1))
    return h

if __name__=="__main__":
    import time
    mp.mp.dps=120
    a=mp.mpf(2)/5; s0=mp.mpf('0.5'); M=40
    t=time.time(); h=hurwitz_taylor(a,s0,M); tb=time.time()-t
    # verify vs mpmath per-order
    t=time.time(); worst=mp.mpf(0)
    for n in [0,1,5,10,20,30,40]:
        ref=mp.zeta(s0,a,n)/mp.factorial(n); rel=abs(h[n]-ref)/abs(ref) if ref!=0 else abs(h[n]-ref)
        worst=max(worst,rel)
        print(f"  n={n:2d}: batch={mp.nstr(h[n],12)}  mpmath={mp.nstr(ref,12)}  rel={mp.nstr(rel,3)}")
    tref=time.time()-t
    print(f"batched (all {M+1} coeffs): {tb:.2f}s ;  mpmath (7 coeffs only): {tref:.2f}s ; worst rel={mp.nstr(worst,3)}")
