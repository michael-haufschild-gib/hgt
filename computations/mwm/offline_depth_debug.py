import numpy as np, mpmath as mp
TWO_PI=2*np.pi; LOG2PI=np.log(TWO_PI)
def slg(z):
    z2=z*z; return (z-0.5)*np.log(z)-z+0.5*LOG2PI+1/(12*z)-1/(360*z*z2)+1/(1260*z*z2*z2)
def g_on_line(N,t):
    s=0.5+1j*t; n=np.arange(1,N+1); logn=np.log(n)
    D=((n**-0.5)[None,:]*np.exp(-1j*np.outer(t,logn))).sum(axis=1)
    return (np.exp(-(s/2)*np.log(np.pi)+slg(s/2))*D).real

N=60; dt=0.01
t=np.arange(TWO_PI*N*N, TWO_PI*(N+0.5)**2, dt)
g=g_on_line(N,t); ag=np.abs(g)
sc=np.where(g[:-1]*g[1:]<0)[0]; zt=t[sc]; gaps=np.diff(zt); medgap=np.median(gaps)
loc=np.where((ag[1:-1]<ag[:-2])&(ag[1:-1]<ag[2:]))[0]+1
print(f"N={N} pts={len(t)} zeros={len(zt)} medgap={medgap:.3f} maxgap={gaps.max():.3f} loc_minima={len(loc)}")
# scale of g
print(f"|g| range [{ag.min():.2e},{ag.max():.2e}]  typical |g| max between zeros ~ {np.median(ag):.3f}")
# non-crossing minima: |g| local min with value well above 0
W=6; nc=[]
for i in loc:
    if i<W or i>len(t)-W-1: continue
    seg=g[i-W:i+W+1]
    if np.any(seg[:-1]*seg[1:]<0): continue
    nc.append((t[i], ag[i]))
print(f"non-crossing |g|-minima (W={W}): {len(nc)}")
if nc:
    vals=np.array([q[1] for q in nc])
    print(f"  their |g_min| values: min={vals.min():.2e} med={np.median(vals):.3e} max={vals.max():.2e}")
    print(f"  (compare typical |g|-between-zeros ~ {np.median(ag):.3f})")
# largest gaps: where are missed pairs?
order=np.argsort(gaps)[::-1]
print("top-5 on-line zero gaps (t, gap, gap/medgap):")
for k in order[:5]:
    print(f"   t={zt[k]:.2f} gap={gaps[k]:.3f} ratio={gaps[k]/medgap:.2f}")
