"""Locate DH off-line zeros: grid-scan |f(sigma+it)| for sigma off 1/2, refine minima."""
import mpmath as mp
mp.mp.dps=30
q=5
chi={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}
chibar={r:mp.conj(v) for r,v in chi.items()}
kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
def Lc(s,cm): return mp.power(q,-s)*mp.fsum(cm[r]*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q))
def f(s): return ((1-1j*kk)/2)*Lc(s,chi)+((1+1j*kk)/2)*Lc(s,chibar)
print(f"# kappa={mp.nstr(kk,8)}")
# verify literature off-line zero near 0.8085 + 85.699 i
for cand in [mp.mpc('0.808517','85.699348'), mp.mpc('0.5','85.699348')]:
    print(f"  |f({mp.nstr(cand,8)})| = {mp.nstr(abs(f(cand)),5)}")
# coarse scan for small |f| off the line, low heights
print("# scan sigma in {0.7,0.9,1.1}, t in (1,100): report local |f| minima < 0.05")
import math
for sig in [mp.mpf('0.7'),mp.mpf('0.9'),mp.mpf('1.1')]:
    t=mp.mpf(1); best=[]
    vals=[]
    while t<100:
        vals.append((t,abs(f(sig+1j*t)))); t+=mp.mpf('0.5')
    for i in range(1,len(vals)-1):
        if vals[i][1]<vals[i-1][1] and vals[i][1]<vals[i+1][1] and vals[i][1]<0.05:
            best.append(vals[i])
    bs=", ".join(f"t≈{mp.nstr(b[0],5)}(|f|={mp.nstr(b[1],2)})" for b in best[:6])
    print(f"  sigma={mp.nstr(sig,3)}: {bs if best else 'no min<0.05'}")
