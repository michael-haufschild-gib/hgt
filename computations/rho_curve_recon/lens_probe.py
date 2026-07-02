"""Lens-clip chains: single-chain viability without covers.
Escapes(D(c,r)): points with |w| > x* escape; the rest lie in the lens D(c,r) cap ball(0,x*),
which is enclosed in an explicit disk (chord midpoint, radius sqrt(h^2+s^2)); recurse on its image.
"""
import numpy as np

def xstar(B): return (1.0+np.sqrt(1.0+4.0*B))/2.0

def lens_enclose(c, r, X):
    """Smallest-ish disk containing D(c,r) cap ball(0,X). Returns None if empty."""
    d = abs(c)
    if d >= X + r:  return None                      # empty
    if d + r <= X:  return (c, r)                    # fully inside
    if d + X <= r:  return (0j, X)                   # ball inside disk
    a = (d*d + X*X - r*r) / (2*d)                    # foot of chord along c-hat
    h2 = X*X - a*a
    h = np.sqrt(max(h2, 0.0))
    s1 = X - a                                       # cap sagitta (ball side)
    s2 = r - (d - a)                                 # cap sagitta (disk side)
    s = max(s1, s2, 0.0)
    p = c/d * a
    return (p, np.sqrt(h*h + s*s) * 1.0000001)

def lens_chain(b, maxd=200):
    X = xstar(abs(b)) * 1.0005
    c, r = 0j, 1.0
    for d in range(maxd):
        # push forward
        r = r*(2*abs(c)+r); c = c*c + b
        if abs(c) - r > X: return d+1
        enc = lens_enclose(c, r, X)
        if enc is None: return d+1                   # whole disk already beyond x*
        c, r = enc
        if r > 3*X: return 0                         # blow-up
    return 0

print("=== lens-clip chains at modulus 3 (the stubborn band + around) ===")
for deg in list(np.arange(90, 158, 2.0)):
    b = 3*np.exp(1j*np.radians(deg))
    d = lens_chain(b)
    s = np.sqrt(1-4*b)
    p1 = min(abs((1+s)/2+b), abs((1-s)/2+b))
    print(f"{deg:6.1f}  lens-chain depth = {d:3d}   p1 = {p1:.4f}")

print("\n=== lens-clip on the ring: how far down does it certify? theta rows ===")
for deg in [0, 30, 60, 75, 90, 105, 120, 135, 150, 165, 180]:
    row = []
    for rr in np.linspace(2.02, 3.44, 25):
        b = rr*np.exp(1j*np.radians(deg))
        row.append("V" if lens_chain(b) else ".")
    print(f"theta={deg:5.1f}  {''.join(row)}")
print("radii:", " ".join(f"{x:.2f}" for x in np.linspace(2.02,3.44,25)[::4]))

print("\n=== positive ray, lens chains near r=2 ===")
for rr in [2.001, 2.01, 2.05, 2.1, 2.2]:
    print(f"  b={rr}: depth={lens_chain(rr+0j)}")
