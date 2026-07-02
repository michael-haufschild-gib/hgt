"""Deeper probe of the unknown band at modulus 3 (94-156 deg): stronger chains + stronger beam."""
import numpy as np

def xstar(B): return (1.0 + np.sqrt(1.0 + 4.0*B))/2.0

def p1_val(b):
    s = np.sqrt(1-4*b)
    return min(abs((1+s)/2+b), abs((1-s)/2+b))

def p2_val(b):
    t = np.sqrt(-3-4*b)
    return min(abs((-1+t)/2-b), abs((-1-t)/2-b))

def beam(b, depth=32, K=1024):
    s = np.sqrt(1-4*b)
    t = np.sqrt(-3-4*b)
    W = np.array([(1+s)/2,(1-s)/2,(-1+t)/2,(-1-t)/2], dtype=complex)
    best = np.min(np.abs(W))
    for _ in range(depth):
        R = np.sqrt(W - b)
        W = np.concatenate([R,-R])
        best = min(best, float(np.min(np.abs(W))))
        if best <= 0.999: return best
        i1 = np.argsort(np.abs(W))[:K]
        i2 = np.argsort(np.abs(W-b))[:K]
        W = W[np.unique(np.concatenate([i1,i2]))]
    return best

def cover(k):
    if k==1: return [0j],1.0
    h=1.0/k; rad=h/np.sqrt(2)*1.02; cs=[]
    for i in range(-k,k+1):
        for j in range(-k,k+1):
            c=complex(i*h,j*h)
            if abs(c)<=1.0+0.75*h: cs.append(c)
    return cs,rad

def chain(b,c0,r0,maxd=80):
    xs=xstar(abs(b))*1.0005; c,r=c0,r0
    for d in range(maxd):
        r=r*(2*abs(c)+r); c=c*c+b
        if abs(c)-r>xs: return d+1
        if r>abs(c): return 0
    return 0

def viable(b,ks=(1,2,4,6,8,12)):
    for k in ks:
        cs,rad=cover(k)
        ds=[chain(b,c,rad) for c in cs]
        if all(d>0 for d in ds): return k,max(ds)
    return 0,0

print("deg   p1_val  p2_val  beam_min   chain(k,d)")
for deg in np.arange(92, 158, 4.0):
    b = 3*np.exp(1j*np.radians(deg))
    k,d = viable(b)
    bm = beam(b)
    print(f"{deg:5.1f}  {p1_val(b):6.3f}  {p2_val(b):6.3f}  {bm:8.4f}   k={k} d={d}")
