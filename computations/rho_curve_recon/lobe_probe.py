"""Identify the mid-angle obstructed lobe: P1 vs P2 vs deeper patterns; probe (2.2, 90deg)."""
import numpy as np

def xstar(B): return (1.0+np.sqrt(1.0+4.0*B))/2.0

def p1(b):
    s=np.sqrt(1-4*b); return min(abs((1+s)/2+b),abs((1-s)/2+b))
def p2(b):
    t=np.sqrt(-3-4*b); return min(abs((-1+t)/2-b),abs((-1-t)/2-b))
def p3(b):
    # period-3 points: roots of (f^3(z)-z)/(f(z)-z) -- degree 6 polynomial; compute f^3(z)-z deg 8, divide out fixed pts numerically via roots of full and filter
    coeffs = np.zeros(9, dtype=complex)  # f^3(z) - z where f = z^2+b
    # f1 = z^2+b; f2 = f1^2+b = z^4+2bz^2+b^2+b; f3 = f2^2+b
    # f2 coeffs (deg4): [1,0,2b,0,b^2+b]
    f2 = np.array([1,0,2*b,0,b*b+b], dtype=complex)
    f3 = np.polymul(f2,f2); f3[-1] += b
    f3z = f3.copy(); f3z[-2] -= 1
    roots = np.roots(f3z)
    per3 = [z for z in roots if abs(z*z+b - z) > 1e-8]   # exclude fixed points
    if not per3: return 9e9
    return min(abs(np.sqrt(g-b)) for g in per3)          # depth-1 preimage modulus = sqrt|g-b|... careful: witness x with x^2+b=g -> x^2 = g-b, |x| = sqrt|g-b|
def pattern_direct(b):
    # min over witnesses: sqrt|p - b| for p in {beta+-, gamma+-, period3 pts} AND the points themselves
    pts = []
    s=np.sqrt(1-4*b); pts += [(1+s)/2,(1-s)/2]
    t=np.sqrt(-3-4*b); pts += [(-1+t)/2,(-1-t)/2]
    f2 = np.array([1,0,2*b,0,b*b+b], dtype=complex)
    f3 = np.polymul(f2,f2); f3[-1]+=b; f3[-2]-=1
    pts += [z for z in np.roots(f3) if abs(z*z+b-z) > 1e-8]
    best = min(abs(p) for p in pts)
    best = min(best, min(np.sqrt(abs(p-b)) for p in pts))
    return best

print("=== mid-angle lobe: which pattern? ===")
print(" (r, deg)      p1      p2     min|witness| (incl per-3 + preimages)")
for rr,deg in [(2.05,75),(2.10,75),(2.05,90),(2.2,90),(2.3,90),(2.05,105),(2.3,105),(2.05,120),(2.5,120),(2.05,60)]:
    b = rr*np.exp(1j*np.radians(deg))
    print(f" ({rr:.2f},{deg:3d})  {p1(b):6.3f}  {p2(b):6.3f}   {pattern_direct(b):6.4f}")

print("\n=== beam (deep) at the anomaly (2.2, 90deg) and neighbors ===")
def beam(b, depth=36, K=2048):
    s=np.sqrt(1-4*b); t=np.sqrt(-3-4*b)
    W=np.array([(1+s)/2,(1-s)/2,(-1+t)/2,(-1-t)/2],dtype=complex)
    best=float(np.min(np.abs(W)))
    for _ in range(depth):
        R=np.sqrt(W-b); W=np.concatenate([R,-R])
        best=min(best,float(np.min(np.abs(W))))
        if best<=0.999: return best
        i1=np.argsort(np.abs(W))[:K]; i2=np.argsort(np.abs(W-b))[:K]
        W=W[np.unique(np.concatenate([i1,i2]))]
    return best
for rr,deg in [(2.2,90),(2.15,90),(2.25,90),(2.2,85),(2.2,95)]:
    b=rr*np.exp(1j*np.radians(deg))
    print(f" ({rr:.2f},{deg:3d}): beam={beam(b):.4f}")

print("\n=== square-tree with big budget at (2.2, 90deg) ===")
def chain_depth(b,c0,r0,maxd=80):
    xs=xstar(abs(b))*1.0005; c,r=c0,r0
    for d in range(maxd):
        r=r*(2*abs(c)+r); c=c*c+b
        if abs(c)-r>xs: return d+1
        if r>abs(c)+xs: return 0
    return 0
def sqt(b,hmin=1e-6,budget=3000000):
    stack=[(0.0,0.0,1.0)]; leaves=0; nodes=0; maxd=0; sd=0
    while stack:
        cx,cy,h=stack.pop(); nodes+=1
        if nodes>budget: return None
        dx=max(abs(cx)-h,0.0); dy=max(abs(cy)-h,0.0)
        if dx*dx+dy*dy>1.0: continue
        d=chain_depth(b,complex(cx,cy),h*np.sqrt(2))
        if d: leaves+=1; maxd=max(maxd,d); continue
        if h<hmin: return None
        sd=max(sd,int(round(-np.log2(h)))+1); h2=h/2
        for sx in (-h2,h2):
            for sy in (-h2,h2): stack.append((cx+sx,cy+sy,h2))
    return leaves,maxd,sd
b=2.2*np.exp(1j*np.radians(90))
res=sqt(b)
print("  (2.2,90):", res if res else "FAILED even at budget 3e6")
