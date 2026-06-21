"""One-time: cache the first N nontrivial zeros to /root/gam_cache.txt at high precision.
All wall-anatomy analyses then load this instead of recomputing zetazero (the only slow step).
args: N dps"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 300
mp.mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 170
fn="/root/gam_cache.txt"
with open(fn,"w") as f:
    f.write(f"{N} {mp.mp.dps}\n")
    for n in range(1,N+1):
        f.write(mp.nstr(mp.zetazero(n).imag, mp.mp.dps+5)+"\n")
print("wrote",fn,"N=",N,"dps=",mp.mp.dps)
