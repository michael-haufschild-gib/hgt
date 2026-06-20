# R4 STEP 8 (minimal-Levenshtein edit of the spectral-flow node script).
# NODE script: eigvalsh of parameterized symmetric matrix D(t)=A cos t+B sin t, swept over ts,
#   readout = signed crossings (spectral flow = a causality/flow quantity).
# MINIMAL EDIT: D(t) -> Gram matrix of HT value-shift vectors; readout -> smallest eigenvalue
#   (VALUE RELATION: min-eig ~ 0 <=> {f(t),...,f(t+N-1)} linearly dependent over poly coeffs).
import numpy as np, mpmath as mp
mp.mp.dps = 40
N = 6
def Dgram(f, t):  # symmetric Gram of shift-vectors v_k(s)=s^? * f(s+k) sampled over s
    ss = [t + 0.31*m for m in range(3*N)]
    V = np.array([[float(mp.re((mp.mpf(s)**0)*f(s+k))) for s in ss] for k in range(N)])  # rows=shifts
    G = V @ V.T
    return G/np.trace(G)*N
ts = np.linspace(1.2, 4.0, 40)
for name,f in [("Gamma (diff-algebraic)", mp.gamma), ("zeta (diff-transcendental)", mp.zeta)]:
    mins = [np.linalg.eigvalsh(Dgram(f,t)).min() for t in ts]
    print(f"{name:30s}: min-eig over sweep  median={np.median(mins):.2e}  min={np.min(mins):.2e}")
# control: an algebraic function (rational) -> strong value relation expected
mins=[np.linalg.eigvalsh(Dgram(lambda s: 1/(mp.mpf(s)+2), t)).min() for t in ts]
print(f"{'control 1/(s+2) (rational)':30s}: min-eig over sweep  median={np.median(mins):.2e}  min={np.min(mins):.2e}")
