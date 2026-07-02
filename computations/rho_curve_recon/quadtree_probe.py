"""Adaptive quadtree escape certificates: split only failing disks.
disk_subset_four: D(c,r) <= union of D(c +- r/2 +- ir/2, r/sqrt2)  (exact containment).
Leaf: plain disk chain escapes past xstar. Count leaves + max chain depth per parameter."""
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

def quadtree(b, c0=0j, r0=1.0, rmin=1e-4, budget=200000):
    stack = [(c0, r0)]
    leaves = 0; maxdepth = 0; maxsplit = 0; nodes = 0
    while stack:
        c, r = stack.pop()
        nodes += 1
        if nodes > budget: return None
        d = chain_depth(b, c, r)
        if d:
            leaves += 1; maxdepth = max(maxdepth, d); continue
        if r < rmin: return None
        maxsplit = max(maxsplit, int(round(np.log(1.0/r)/np.log(np.sqrt(2)))))
        h = r/2
        for dc in (h+1j*h, h-1j*h, -h+1j*h, -h-1j*h):
            stack.append((c+dc, r/np.sqrt(2)))
    return leaves, maxdepth, maxsplit

print("=== quadtree certificates at modulus 3 ===")
for deg in [90, 100, 110, 120, 130, 136, 140, 144, 148, 150, 152, 153, 154, 155, 155.5]:
    b = 3*np.exp(1j*np.radians(deg))
    res = quadtree(b)
    if res:
        print(f"  {deg:6.1f} deg: leaves={res[0]:5d}  max chain depth={res[1]:2d}  max split depth={res[2]}")
    else:
        print(f"  {deg:6.1f} deg: FAILED (budget/rmin)")

print("\n=== quadtree down the positive ray ===")
for rr in [2.001, 2.005, 2.02, 2.05, 2.1, 2.3, 2.7]:
    res = quadtree(rr+0j)
    print(f"  b={rr:6.3f}: " + (f"leaves={res[0]:5d} chain_d={res[1]} split_d={res[2]}" if res else "FAILED"))

print("\n=== quadtree at ring corners (low radius, various angles) ===")
for deg, rr in [(30,2.05),(60,2.05),(75,2.1),(90,2.2),(105,2.4),(120,2.6),(135,2.9),(150,3.2),(165,3.35),(170,3.4)]:
    b = rr*np.exp(1j*np.radians(deg))
    res = quadtree(b)
    s = np.sqrt(1-4*b); p1 = min(abs((1+s)/2+b), abs((1-s)/2+b))
    print(f"  ({rr:.2f}, {deg:5.1f}deg): " + (f"leaves={res[0]:5d} d={res[1]}" if res else "FAILED    ") + f"  p1={p1:.3f}")
