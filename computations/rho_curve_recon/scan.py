"""[rho.1] Reconnaissance of the dichotomy ring for the critical curve rho(arg b).

Verdicts per parameter b:
  OBSTRUCTED  — K_b meets the closed unit disk. Detected by (i) closed-form pattern regions
                P1: min± |(1+s)/2 + b| <= 1, s^2 = 1-4b   (preimage of fixed point beta)
                P2: min± |gamma - b| <= 1, gamma^2+gamma+b+1 = 0 (preimage of the 2-cycle)
                and (ii) a beam search over the inverse-orbit tree of beta (any node is a
                genuine K_b point; min modulus <= 1 - eps => obstructed witness).
  VIABLE      — closed unit disk escapes: disk-arithmetic chains D(c,r) -> D(c^2+b, r(2|c|+r)),
                success when |c| - r > xstar(|b|); with k-fold covers of D(0,1) when needed.
  UNKNOWN     — neither certificate found at recon depth.
"""
import numpy as np

def xstar(B):  # escape fixed point of t -> t^2 - B
    return (1.0 + np.sqrt(1.0 + 4.0 * B)) / 2.0

# ---------- obstruction: closed-form patterns ----------
def p1_val(b):
    s = np.sqrt(1 - 4 * b)          # principal branch; other root is -s
    return np.minimum(np.abs((1 + s) / 2 + b), np.abs((1 - s) / 2 + b))

def p2_val(b):
    t = np.sqrt(-3 - 4 * b)
    g1 = (-1 + t) / 2
    g2 = (-1 - t) / 2
    return np.minimum(np.abs(g1 - b), np.abs(g2 - b))

# ---------- obstruction: beam over the inverse-orbit tree of beta ----------
def beam_min_modulus(b, depth=18, K=96):
    s = np.sqrt(1 - 4 * b)
    W = np.array([ (1 + s) / 2, (1 - s) / 2 ], dtype=complex)   # both fixed points
    best = np.min(np.abs(W))
    for _ in range(depth):
        R = np.sqrt(W - b)
        W = np.concatenate([R, -R])
        best = min(best, np.min(np.abs(W)))
        if best <= 0.999:
            return best
        # beam prune: keep K smallest by |w| and K smallest by |w - b| (children moduli = sqrt|w-b|)
        i1 = np.argsort(np.abs(W))[:K]
        i2 = np.argsort(np.abs(W - b))[:K]
        W = W[np.unique(np.concatenate([i1, i2]))]
    return best

# ---------- viability: disk chains with covers ----------
def cover_centers(k):
    if k == 1:
        return [0j], 1.0
    h = 1.0 / k
    rad = h / np.sqrt(2) * 1.02
    cs = []
    rng = np.arange(-k, k + 1)
    for i in rng:
        for j in rng:
            c = complex(i * h, j * h)
            if abs(c) <= 1.0 + h * 0.75:
                cs.append(c)
    return cs, rad

def chain_escapes(b, c0, r0, maxdepth=40):
    xs = xstar(abs(b)) * 1.001
    c, r = c0, r0
    for d in range(maxdepth):
        c = c * c + b if d > 0 else c0 * c0 + b   # step
        r = r * (2 * abs(c0) + r) if d > 0 else r0 * (2 * abs(c0) + r0)
        # NOTE: must use previous center modulus; rewrite cleanly below
        raise RuntimeError
    return False

def chain_escapes(b, c0, r0, maxdepth=40):   # clean version
    xs = xstar(abs(b)) * 1.001
    c, r = c0, r0
    for d in range(maxdepth):
        r = r * (2 * abs(c) + r)
        c = c * c + b
        if abs(c) - r > xs:
            return d + 1
        if r > abs(c):
            return 0
    return 0

def viable_depth(b, ks=(1, 2, 4)):
    for k in ks:
        cs, rad = cover_centers(k)
        depths = [chain_escapes(b, c, rad) for c in cs]
        if all(d > 0 for d in depths):
            return k, max(depths)
    return 0, 0

def verdict(b):
    if p1_val(np.array([b]))[0] <= 1.0:
        return "OBST-P1"
    if p2_val(np.array([b]))[0] <= 1.0:
        return "OBST-P2"
    k, d = viable_depth(b)
    if k:
        return f"VIAB-k{k}d{d}"
    if beam_min_modulus(b) <= 0.999:
        return "OBST-BEAM"
    return "UNKNOWN"

# ============ Part 1: ring scan ============
print("=== ring scan 2.05 <= |b| <= 3.6, theta in [0,pi] (verdict classes) ===")
thetas = np.linspace(0, np.pi, 37)
radii = np.linspace(2.05, 3.6, 16)
rows = {}
for th in thetas:
    row = []
    for r in radii:
        v = verdict(r * np.exp(1j * th))
        row.append(v[0] if v != "UNKNOWN" else "?")   # V / O / ?
    rows[th] = "".join(row)
    print(f"theta={np.degrees(th):6.1f}  " + rows[th])
print("radii:", " ".join(f"{r:.2f}" for r in radii))

# ============ Part 2: positive ray ============
print("\n=== positive ray: real b in (2, 2+sqrt2], beam min modulus of K_b ===")
worst = (9e9, None)
for br in np.linspace(2.01, 2 + np.sqrt(2), 30):
    m = beam_min_modulus(br + 0j, depth=24, K=128)
    if m < worst[0]:
        worst = (m, br)
print(f"min over ray of (min|x|, x in K_b tree) = {worst[0]:.4f} at b = {worst[1]:.4f}"
      f"  -> {'OBSTRUCTION ON POSITIVE RAY!' if worst[0] <= 1 else 'ray looks viable (no witness <= 1)'}")

# ============ Part 3: modulus-3 circle, fine ============
print("\n=== modulus 3 circle, fine sweep (0.5 deg) ===")
prev = None
for deg in np.arange(0, 180.01, 0.5):
    b = 3 * np.exp(1j * np.radians(deg))
    v = verdict(b)
    tag = v.split("-")[0]
    if tag != prev:
        print(f"  {deg:6.1f} deg : {v}")
        prev = tag

# ============ Part 4: negative ray above threshold (for rho.8) ============
print("\n=== negative ray: real b < -(2+sqrt2), viability by chains ===")
for br in [-3.43, -3.5, -3.6, -3.8, -4.0, -4.5]:
    k, d = viable_depth(br + 0j, ks=(1, 2, 4, 6, 8))
    bm = beam_min_modulus(br + 0j, depth=24, K=128)
    print(f"  b={br:6.2f}: chain viable k={k} depth={d};  beam min|x| = {bm:.4f}")
