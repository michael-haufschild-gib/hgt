# Pre-certify (htail) for the physical section class delta_j = c/j:
#   T_A := sum_{k<R} (wA_k/2) csch^2(newA_k/2) <= T_B := sum_{k<R} (wB_k/2) csch^2(oldB_k/2)
# over c in {1,1.5,2,3}, d in {100,200,400}, i outer half (R<=L), theta = s/delta in [0.15,0.5].
# Also locate theta_min(c) where htail first holds (rank-0 crossover).
from mpmath import mp, mpf, sinh
mp.dps = 30
def csch2(x): return 1/sinh(x)**2
def TB_TA(c, d, i, theta):
    g = [None]+[mpf(c)/j for j in range(1, d+1)]
    t = [None, mpf(0)]
    for j in range(1, d): t.append(t[j]+g[j])
    s = theta*g[i+1]; L, R = i, d-i-2
    TB = TA = mpf(0)
    for k in range(R):
        oldB = t[i+1]-t[i-k]-s;  newB = t[i+2]-t[i+1-k]-s
        newA = t[i+2+k]-t[i+1]+s + (t[i+3+k]-t[i+2]) - (t[i+2+k]-t[i+1])  # recompute cleanly below
        newA = t[i+3+k]-t[i+2]+s; oldA = t[i+2+k]-t[i+1]+s
        wB = oldB-newB; wA = oldA-newA
        TB += (wB/2)*csch2(oldB/2); TA += (wA/2)*csch2(newA/2)
    return float(TB), float(TA)
print("=== htail margin T_B - T_A (must be >= 0) ===")
worst = {}
for c in (1, 1.5, 2, 3):
    w = None
    for d in (100, 200, 400):
        for frac in (0.50, 0.60, 0.75, 0.90, 0.97):
            i = int(d*frac)
            if d-i-2 < 1 or d-i-2 > i: continue
            for theta in (0.15, 0.2, 0.25, 0.29, 0.38, 0.5):
                TB, TA = TB_TA(c, d, i, theta)
                m = TB - TA
                if w is None or m < w[0]: w = (m, d, frac, theta, TB, TA)
    worst[c] = w
    print(f"c={c}: worst margin {w[0]:+.4f} at d={w[1]} i={w[2]}d theta={w[3]}  (T_B={w[4]:.3f} T_A={w[5]:.3f})")
print("\n=== theta_min: smallest theta with htail>=0, c=2, d=200, i=0.5d ===")
d, i = 200, 100
lo, hi = 0.0, 0.5
for _ in range(30):
    mid = (lo+hi)/2
    TB, TA = TB_TA(2, d, i, mid)
    if TB - TA >= 0: hi = mid
    else: lo = mid
print(f"theta_min ~ {hi:.4f}")
