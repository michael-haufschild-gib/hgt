"""Falsification battery for the two-Volterra domination loop, cycle 1.

Q(G) for packet G = sum c_j e^{w_j x} equals the Bezoutian form of the kernel transform F:
  M_{jk} = [F'(w_j) conj(F(w_k)) + F(w_j) conj(F'(w_k))]/(w_j + conj(w_k)),  Re w > 1/2.
E1: kill C1 (even+positive+log-concave insufficient) via F1 = Gaussian*(1+0.2 cos x).
E2: symmetrized one-atom F_even: off-axis zero scan + PSD battery.
E3: causal two/three-atom truncation (1+2^{-1/2-w})F_g: expect indefinite.
E3b: EVEN-symmetrized N-atom truncations: PSD? (new conjecture probe), N = 1,2,3,5,10.
"""
import json, random, sys
import mpmath as mp

mp.mp.dps = 40
PI = mp.pi

def Fg(w):
    return PI**(mp.mpf(-1)/4) * PI**(-w/2) * mp.gamma(w/2 + mp.mpf(5)/4) * (w - mp.mpf(1)/2)

def dF(F, w):
    h = mp.mpf(10)**(-12)
    return (8*(F(w+h)-F(w-h)) - (F(w+2*h)-F(w-2*h)))/(12*h)

def bez_min_eig(F, nodes):
    vals = [(F(w), dF(F, w)) for w in nodes]
    n = len(nodes)
    M = mp.matrix(n, n)
    for j in range(n):
        fj, dj = vals[j]
        for k in range(n):
            fk, dk = vals[k]
            M[j, k] = (dj*mp.conj(fk) + fj*mp.conj(dk))/(nodes[j] + mp.conj(nodes[k]))
    E = mp.eighe(M, eigvals_only=True)
    ev = sorted(mp.re(e) for e in E)
    return ev[0], ev[-1]

def hunt_negative(F, region, ranks=(2,3,4), tries=120, seed=1):
    rng = random.Random(seed)
    best = None
    for r in ranks:
        for _ in range(tries):
            nodes = [mp.mpc(region[0]+ (region[1]-region[0])*rng.random(),
                            region[2] + (region[3]-region[2])*rng.random()) for _ in range(r)]
            try:
                lo, hi = bez_min_eig(F, nodes)
            except Exception:
                continue
            rel = lo/abs(hi) if hi != 0 else lo
            if best is None or rel < best[0]:
                best = (rel, r, [(float(mp.re(z)), float(mp.im(z))) for z in nodes])
    return best

print("== E1: C1 kill — Gaussian*(1+0.2cos x), even positive log-concave ==")
def F1(w):
    return mp.sqrt(2*PI)*(mp.e**(w**2/2) + mp.mpf('0.1')*(mp.e**((w+1j)**2/2) + mp.e**((w-1j)**2/2)))
# log-concavity check of phi1 on grid
worst_lc = None
for i in range(-400, 401):
    x = mp.mpf(i)/50
    c = mp.cos(x)
    val = -1 - mp.mpf('0.2')*(c + mp.mpf('0.2'))/(1+mp.mpf('0.2')*c)**2  # (log phi1)''
    if worst_lc is None or val > worst_lc:
        worst_lc = val
print("max (log phi1)'' on [-8,8]:", mp.nstr(worst_lc, 6), "(must be < 0)")
# zero of F1 near pi + 2.79i: 1 + 0.2 e^{-1/2} cos w = 0
w0 = mp.findroot(lambda w: 1 + mp.mpf('0.2')*mp.e**(mp.mpf(-1)/2)*mp.cos(w), mp.mpc(3.14, 2.8))
print("off-axis zero of F1 at w0 =", mp.nstr(w0, 10), " Re>1/2:", mp.re(w0) > 0.5)
best1 = hunt_negative(F1, (max(0.51, mp.re(w0)-1.2), mp.re(w0)+1.2, mp.im(w0)-1.2, mp.im(w0)+1.2))
print("E1 best rel min eig:", mp.nstr(best1[0], 6), "rank", best1[1], "nodes", best1[2])

print()
print("== E2: symmetrized one-atom F_even ==")
def Feven(w):
    return (Fg(w) + Fg(-w))/2
# argument principle box scan for off-axis zeros in Re in (0.05, 8], Im in [0, 50]
def count_zeros_box(F, x0, x1, y0, y1, npts=260):
    tot = mp.mpc(0)
    corners = [mp.mpc(x0,y0), mp.mpc(x1,y0), mp.mpc(x1,y1), mp.mpc(x0,y1), mp.mpc(x0,y0)]
    for a, b in zip(corners[:-1], corners[1:]):
        prev = None
        acc = mp.mpf(0)
        for i in range(npts+1):
            z = a + (b-a)*mp.mpf(i)/npts
            ph = mp.arg(F(z))
            if prev is not None:
                d = ph - prev
                while d > PI: d -= 2*PI
                while d < -PI: d += 2*PI
                acc += d
            prev = ph
        tot += acc
    return tot/(2*PI)
nz = count_zeros_box(Feven, 0.05, 8, 0.2, 50)
print("zeros of F_even in box Re(0.05,8) x Im(0.2,50):", mp.nstr(nz, 6))
nz2 = count_zeros_box(Feven, 0.05, 8, -50, -0.2)
print("zeros in conjugate box:", mp.nstr(nz2, 6))
best2 = hunt_negative(Feven, (0.51, 4.0, -30, 30), ranks=(2,4,6,8), tries=150, seed=3)
print("E2 best rel min eig (want >= 0):", mp.nstr(best2[0], 6), "rank", best2[1])

print()
print("== E3: causal truncations zeta_N(w+1/2) Fg(w) ==")
for N in (2, 3):
    def FN(w, N=N):
        return sum(mp.mpf(n)**(-(w+mp.mpf(1)/2)) for n in range(1, N+1)) * Fg(w)
    b = hunt_negative(FN, (0.51, 3.0, -25, 25), ranks=(2,3,4), tries=120, seed=10+N)
    print(f"N={N} causal best rel min eig:", mp.nstr(b[0], 6), "rank", b[1], "nodes", b[2] if b[0] < 0 else "")

print()
print("== E3b: EVEN-symmetrized truncations (1/2)[zeta_N(w+1/2)Fg(w) + zeta_N(1/2-w)Fg(-w)] ==")
for N in (1, 2, 3, 5, 10):
    def FNe(w, N=N):
        zN1 = sum(mp.mpf(n)**(-(w+mp.mpf(1)/2)) for n in range(1, N+1))
        zN2 = sum(mp.mpf(n)**(-(mp.mpf(1)/2-w)) for n in range(1, N+1))
        return (zN1*Fg(w) + zN2*Fg(-w))/2
    b = hunt_negative(FNe, (0.51, 2.2, -25, 25), ranks=(2,3,4,6), tries=150, seed=20+N)
    print(f"N={N} even-trunc best rel min eig:", mp.nstr(b[0], 6), "rank", b[1],
          ("NEG nodes " + str(b[2])) if b[0] < 0 else "")
