# B-v2 (method 20). Missing lemma: is the signal exponent a INTRINSIC or a Hann-WINDOW artifact?
# Measure a under 3 windows (boxcar, Hann, Gaussian). Window-invariant a => intrinsic lemma.
import mpmath as mp, numpy as np, math
Nmax=800
gam=np.array([float(mp.im(mp.zetazero(n))) for n in range(1,Nmax+1)])
us=[math.log(p) for p in [2,3,5,7,11]]
def box(N): return np.ones(N)
def hann(N): return np.array([0.5-0.5*math.cos(2*math.pi*i/(N-1)) for i in range(N)])
def gauss(N): x=(np.arange(N)-N/2)/(N/4); return np.exp(-0.5*x*x)
ladder=[100,200,400,800]
for nm,wf in [("box",box),("hann",hann),("gauss",gauss)]:
    sig=[np.mean([abs(float(np.sum(wf(N)*np.cos(gam[:N]*u)))) for u in us]) for N in ladder]
    a=np.polyfit(np.log(ladder),np.log(sig),1)[0]; print(f"window={nm:6s}: signal exponent a={a:.3f}")
print("LEMMA: a window-invariant => intrinsic signal growth; a varies with window => the 'growth' is a windowing artifact.")
