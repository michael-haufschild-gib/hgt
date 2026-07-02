"""Square-subdivision escape certificates (zero inflation).
Cover [-1,1]^2 >= closed unit disk; split squares exactly into 4; prune squares fully outside
the unit disk; leaf: square (center c, half-side h) within enclosing disk D(c, h*sqrt2) whose
chain escapes past xstar."""
import numpy as np

def xstar(B): return (1.0+np.sqrt(1.0+4.0*B))/2.0

def chain_depth(b, c0, r0, maxd=60):
    xs = xstar(abs(b))*1.0005
    c, r = c0, r0
    for d in range(maxd):
        r = r*(2*abs(c)+r); c = c*c+b
        if abs(c)-r > xs: return d+1
        if r > abs(c)+xs: return 0
    return 0

def outside_unit(cx, cy, h):
    dx = max(abs(cx)-h, 0.0); dy = max(abs(cy)-h, 0.0)
    return dx*dx+dy*dy > 1.0

def squaretree(b, hmin=1e-5, budget=400000):
    stack = [(0.0, 0.0, 1.0)]
    leaves=0; maxd=0; deepest=0; nodes=0; pruned=0
    while stack:
        cx, cy, h = stack.pop()
        nodes += 1
        if nodes > budget: return None
        if outside_unit(cx, cy, h):
            pruned += 1; continue
        d = chain_depth(b, complex(cx,cy), h*np.sqrt(2))
        if d:
            leaves += 1; maxd = max(maxd, d); continue
        if h < hmin: return None
        deepest = max(deepest, int(round(-np.log2(h)))+1)
        h2 = h/2
        for sx in (-h2, h2):
            for sy in (-h2, h2):
                stack.append((cx+sx, cy+sy, h2))
    return leaves, pruned, maxd, deepest

print("=== square-tree certificates at modulus 3 ===")
for deg in [90, 100, 110, 120, 130, 140, 145, 150, 152, 154, 155, 155.5]:
    b = 3*np.exp(1j*np.radians(deg))
    res = squaretree(b)
    print(f"  {deg:6.1f} deg: " + (f"leaves={res[0]:6d} pruned={res[1]:5d} chain_d={res[2]:2d} split_d={res[3]}" if res else "FAILED"))

print("\n=== positive ray ===")
for rr in [2.001, 2.01, 2.05, 2.1, 2.3]:
    res = squaretree(rr+0j)
    print(f"  b={rr:6.3f}: " + (f"leaves={res[0]:6d} pruned={res[1]:5d} chain_d={res[2]} split_d={res[3]}" if res else "FAILED"))

print("\n=== low-radius ring points ===")
for deg, rr in [(60,2.05),(75,2.1),(90,2.2),(105,2.4),(120,2.6),(135,2.9),(150,3.2),(165,3.35)]:
    b = rr*np.exp(1j*np.radians(deg))
    res = squaretree(b)
    print(f"  ({rr:.2f},{deg:5.1f}): " + (f"leaves={res[0]:6d} split_d={res[3]} chain_d={res[2]}" if res else "FAILED"))
