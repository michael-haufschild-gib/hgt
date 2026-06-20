# THE MACHINE R4 (dyson). NODE = Spectral sections for families over parameter spaces.
# STEP 6: probe the constraint on a real self-adjoint family D(t).
#  - spectral flow = signed # eigenvalue crossings of the reference level 0.
#  - a spectral section (continuous projection pinned to P_{>0} outside [-R,R]) exists iff we can
#    cut in a persistent spectral GAP; the naive cut at 0 JUMPS rank at each crossing.
import numpy as np
rng = np.random.default_rng(7)
N = 8
A = rng.standard_normal((N,N)); A = (A+A.T)/2     # fixed symmetric
B = rng.standard_normal((N,N)); B = (B+B.T)/2
def D(t):  # path of self-adjoint operators
    return A*np.cos(t) + B*np.sin(t) - 0.0*np.eye(N)
ts = np.linspace(0, np.pi, 1200)
EV = np.array([np.linalg.eigvalsh(D(t)) for t in ts])   # sorted ascending each row

# spectral flow through 0 (signed crossings of any branch)
sf = 0
for j in range(N):
    s = EV[:,j]
    for k in range(len(ts)-1):
        if s[k] < 0 <= s[k+1]: sf += 1     # up-crossing
        elif s[k] >= 0 > s[k+1]: sf -= 1   # down-crossing
print("net spectral flow through 0 over path:", sf)

# rank below the naive 0-cut: # eigenvalues < 0 (discontinuous when a branch crosses 0)
ranks0 = (EV < 0).sum(axis=1)
print("rank(P_{<0}) range over path:", ranks0.min(), "..", ranks0.max(), " -> jumps:", len(np.unique(ranks0))>1)

# spectral section test: does a constant cut c sit in a GAP for ALL t (=> continuous section)?
def cut_in_gap_always(c):
    for t in ts:
        ev = np.linalg.eigvalsh(D(t))
        # gap means c not within tol of any eigenvalue and same #below for all t
        if np.min(np.abs(ev - c)) < 1e-3: return False
    ranks = np.array([ (np.linalg.eigvalsh(D(t)) < c).sum() for t in ts ])
    return len(np.unique(ranks))==1
maxspec = EV.max()
for c in [0.0, maxspec+0.5, 2.5, -2.5]:
    print(f"  cut c={c:+.2f}: continuous spectral section? {cut_in_gap_always(c)}")
