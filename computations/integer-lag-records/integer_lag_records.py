import numpy as np, math, json, sys, time
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
t0 = time.time()
# von Mangoldt via sieve of smallest prime factor
spf = np.zeros(N + 1, dtype=np.int64)
for p in range(2, int(N ** 0.5) + 1):
    if spf[p] == 0:
        spf[p * p::p][spf[p * p::p] == 0] = p
idx = np.arange(N + 1)
spf[spf == 0] = idx[spf == 0]
spf[0] = 0; spf[1] = 0
# Λ(n) = log p if n = p^k
Lam = np.zeros(N + 1)
n = idx.copy()
mask = np.ones(N + 1, dtype=bool); mask[:2] = False
p = spf.copy()
q = n.copy()
# strip all factors p; prime power iff remainder is 1
for _ in range(30):
    sel = mask & (q % np.where(p > 0, p, 1) == 0) & (q > 1)
    if not sel.any():
        break
    q[sel] //= p[sel]
is_pp = mask & (q == 1)
Lam[is_pp] = np.log(p[is_pp].astype(float))
gamma = 0.5772156649015328606
c0 = 2 + gamma - math.log(4 * math.pi)
psi = np.cumsum(Lam)
M = np.cumsum(Lam / np.maximum(idx, 1))
nn = idx[2:].astype(float)
logn = np.log(nn)
S = sum(nn ** (-2 * k) / (2 * k * (2 * k + 1)) for k in range(1, 30))
a = ((nn - psi[2:]) + nn * (M[2:] - logn + gamma) - math.log(2 * math.pi) + S) / np.sqrt(nn)
out = {"N": N, "c0": c0, "max_a": float(a.max()), "argmax": int(a.argmax() + 2), "min_a": float(a.min()), "argmin": int(a.argmin() + 2),
       "frac_of_ceiling_max": float(a.max() / c0), "frac_of_ceiling_min": float(a.min() / c0)}
# record highs
rec = []; best = -1e9
for i, v in enumerate(a):
    if v > best:
        best = v; rec.append((i + 2, float(v)))
out["records"] = rec[-25:]
out["powers_of_2"] = [(2 ** m, float(a[2 ** m - 2])) for m in range(1, int(math.log2(N)) + 1)]
out["powers_of_10"] = [(10 ** k, float(a[10 ** k - 2])) for k in range(1, int(math.log10(N)) + 1)]
out["count_ge_0.9c0"] = int((a >= 0.9 * c0).sum())
out["count_gt_c0"] = int((a > c0).sum())
out["time_s"] = time.time() - t0
print(json.dumps(out, indent=1))
