#!/usr/bin/env python3
"""
Follow-up: the flex-direction PROPAGATION overlap separated zeta(~1.0) from
FID(~0.80) -- but FID is the WRONG null (different density). Re-test against
DENSITY-MATCHED nulls: jittered-zeta (keeps density+rough positions, destroys
exact arithmetic) and RvM-smooth picket-fence (pure density, no arithmetic, no
level repulsion). Plus same-density GUE-ish via jitter.

Observable: softest-eigenvector(H_d) . softest-eigenvector(H_{d+1}) overlap,
H_d[i,j]=T_{i+j+1}, T_k = 2 sum gamma^{-2k}.

Verdict logic (project's own null-control discipline):
  zeta locks (~1.0) AND all density-matched nulls also lock -> GENERIC (spacing), reduces.
  zeta locks AND density-matched nulls rotate (<1) -> RH-ARITHMETIC signal (new).
"""
import mpmath as mp
import random

mp.mp.dps = 50
NZ = 120
KMAX = 22
DMAX = 9
random.seed(410091500312701155)  # rng-drawn session seed

print(f"dps={mp.mp.dps} NZ={NZ} DMAX={DMAX}")
print("computing real zeros...")
gam = [mp.im(mp.zetazero(n)) for n in range(1, NZ + 1)]

# --- density-matched surrogates ---
# RvM smooth: solve N(t)=n-0.5, N(t)=t/(2pi)(log(t/2pi)-1)+7/8
def Ncount(t):
    return t / (2 * mp.pi) * (mp.log(t / (2 * mp.pi)) - 1) + mp.mpf(7) / 8
def rvm_gamma(n):
    # invert N(t)=n-0.5
    guess = 2 * mp.pi * n / mp.log(n + 2)
    return mp.findroot(lambda t: Ncount(t) - (n - mp.mpf('0.5')), max(guess, mp.mpf(10)))
print("computing RvM smooth picket-fence...")
gam_rvm = [rvm_gamma(n) for n in range(1, NZ + 1)]

def jitter(gammas, eps):
    return [g * (1 + eps * (2 * random.random() - 1)) for g in gammas]
gam_j02 = jitter(gam, 0.02)
gam_j10 = jitter(gam, 0.10)

def moments(gammas, kmax):
    return [2 * mp.fsum((g ** (-2 * k) for g in gammas)) for k in range(1, kmax + 1)]

def hankel(T, d):
    return mp.matrix([[T[i + j] for j in range(d)] for i in range(d)])

def softest_vec(H):
    vals, vecs = mp.eigsy(H, eigvals_only=False)
    imin = min(range(len(vals)), key=lambda i: vals[i])
    return [vecs[r, imin] for r in range(H.rows)], vals[imin], max(vals)

def flexprop(T):
    prev = None
    out = []
    for d in range(2, DMAX + 1):
        v, lmin, lmax = softest_vec(hankel(T, d))
        if prev is not None:
            n = min(len(prev), len(v))
            a = v[:n]; b = prev[:n]
            na = mp.sqrt(mp.fsum(x * x for x in a)); nb = mp.sqrt(mp.fsum(x * x for x in b))
            o = abs(mp.fsum(a[i] * b[i] for i in range(n)) / (na * nb)) if na and nb else mp.mpf('nan')
        else:
            o = mp.mpf('nan')
        out.append((d, o))
        prev = v
    return out

variants = {
    "zeta_real": moments(gam, KMAX),
    "jitter_2%": moments(gam_j02, KMAX),
    "jitter_10%": moments(gam_j10, KMAX),
    "RvM_smooth": moments(gam_rvm, KMAX),
}

results = {name: flexprop(T) for name, T in variants.items()}

print("\n=== flex-direction propagation overlap (softest-mode, consecutive d) ===")
hdr = "  d | " + " ".join(f"{name:>11}" for name in variants)
print(hdr)
for idx in range(DMAX - 1):
    d = results["zeta_real"][idx][0]
    row = f"{d:>3} | "
    for name in variants:
        o = results[name][idx][1]
        row += f"{mp.nstr(o,6):>11} "
    print(row)

print("\nVERDICT:")
zs = [results['zeta_real'][i][1] for i in range(1, DMAX - 1)]
print(f"  zeta overlaps (d>=3): {[mp.nstr(x,5) for x in zs]}")
for name in ["jitter_2%", "jitter_10%", "RvM_smooth"]:
    ns = [results[name][i][1] for i in range(1, DMAX - 1)]
    print(f"  {name:>11} overlaps: {[mp.nstr(x,5) for x in ns]}")
print("  -> if density-matched nulls also ~1.0: GENERIC (spacing geometry, reduces).")
print("  -> if only zeta ~1.0: candidate RH-arithmetic signal in flex propagation.")
