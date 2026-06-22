import sys, time, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 80
DPS=int(sys.argv[2]) if len(sys.argv)>2 else 520
mp.mp.dps=DPS
t=time.time(); out=[]; worst=mp.mpf(0)
for n in range(1,N+1):
    z=mp.zetazero(n); g=z.imag
    out.append(mp.nstr(g, DPS-8))
    if n in (1,N//2,N):
        v=abs(mp.zeta(mp.mpf('0.5')+1j*g))
        worst=max(worst,v)
with open('zeros.txt','w') as f: f.write('\n'.join(out)+'\n')
print(f"wrote {N} zeros at dps={DPS} in {time.time()-t:.1f}s; max|zeta(1/2+ig)| sampled = {mp.nstr(worst,3)}")
