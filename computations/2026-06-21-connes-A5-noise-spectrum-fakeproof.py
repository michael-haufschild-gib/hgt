# A5-vB (method 19). Fake proof's "noise~sqrt(N) iid" tested by contrasting gap-SHUFFLE noise with
# TRUE iid uniform-phase noise. If shuffle>iid, gaps retain structure => fake proof's iid assumption is the gap.
import mpmath as mp, numpy as np, math
Nmax=600
gam=[float(mp.im(mp.zetazero(n))) for n in range(1,Nmax+1)]; gaps=np.diff(gam); g0=gam[0]
rng=np.random.default_rng(1402749634)
us=[math.log(p) for p in [2,3,5,7,11]]
def hann(N): return np.array([0.5-0.5*math.cos(2*math.pi*i/(N-1)) for i in range(N)])
def reson(arr,N,u): w=hann(N); return float(np.sum(w*np.cos(np.array(arr[:N])*u)))
for N in [150,300,600]:
    shuf=[np.concatenate([[g0],g0+np.cumsum(rng.permutation(gaps))]) for _ in range(50)]
    iidp=[rng.uniform(0,gam[N-1],N) for _ in range(50)]   # true iid positions, same range
    rs=np.sqrt(np.mean([reson(s,N,u)**2 for s in shuf for u in us]))
    ri=np.sqrt(np.mean([reson(s,N,u)**2 for s in iidp for u in us]))
    print(f"N={N}: shuffle-noise={rs:.3f}  iid-noise={ri:.3f}  ratio={rs/ri:.2f}")
print("GAP: ratio>1 means gap-shuffle noise is super-iid (retained gap structure), breaking the fake proof's sqrt(N).")
