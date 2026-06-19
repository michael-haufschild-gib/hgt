# Gap-labelling = dynamical period quantization (foundations 25.4).
# The almost-Mathieu cocycle is the field's pure rank-2 simple object (24.2); its rotation
# number = integrated density of states (IDS). Gap-labelling theorem (Bellissard/Johnson-Moser):
# IDS at spectral gaps lies in Z+Z*alpha (the arithmetic module of the frequency = Galois data)
# = a proven case of the dynamical period conjecture (25.2).
# IDS via Sturm/LDL pivot sign-count for the tridiagonal operator (no numpy).
# Run: runpod 157.157.221.29:39437, python3 (3.8.10), pure math. 2026-06-19.
import math
alpha = (math.sqrt(5.0)-1.0)/2.0   # golden mean
lam = 1.0                          # critical almost-Mathieu (self-dual)
N = 20000

def count_below(E):
    cnt = 0; d = 1.0
    for n in range(N):
        a = 2.0*lam*math.cos(2.0*math.pi*alpha*n) - E
        if n == 0:
            d = a
        else:
            if d == 0.0: d = 1e-30
            d = a - 1.0/d
        if d < 0.0: cnt += 1
    return cnt

def ids(E):
    return count_below(E)/N

Es = [(-4.0 + 8.0*k/800) for k in range(801)]
vals = [(E, ids(E)) for E in Es]

print("=== almost-Mathieu (lam=1 critical, golden alpha) gap-labelling: IDS at gaps in Z+Z*alpha? ===")
def near_module(x, K=6):
    best=(9,0,0)
    for k in range(-K,K+1):
        y = k*alpha
        m = round(x - y)
        d = abs(x - (y+m))
        if d < best[0]: best=(d,k,m)
    return best
prev=None; gapcount=0
for i in range(1,len(vals)-1):
    E,v = vals[i]
    if abs(vals[i+1][1]-vals[i-1][1]) < 1.0/N*3 and v not in (0.0,1.0):
        d,k,m = near_module(v)
        if d < 0.01 and (prev is None or abs(v-prev)>0.01):
            print("  gap at E=%+.3f : IDS=%.5f   ~ %d*alpha + %d  (dist %.2e)" % (E, v, k, m, d))
            prev=v; gapcount+=1
print("alpha = %.6f ;  detected labelled gaps: %d" % (alpha, gapcount))
