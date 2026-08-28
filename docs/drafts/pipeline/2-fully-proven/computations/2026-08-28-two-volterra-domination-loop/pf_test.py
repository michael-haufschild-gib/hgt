"""Two-atom PF cone test: finite-section singular values of the weighted Wiener-Hopf
operator I + q*2^beta*J^m (q = 2^{-1/2}, shift a = log 2 discretized as m cells), and
the Bohr almost-zero driver for the full operator (min |zeta| on a strip line)."""
import numpy as np

q = 2**-0.5
m = 64          # cells per shift log2
for beta in (0.30, 0.45, 0.50, 0.55, 0.70):
    r = q * 2**beta
    row = []
    for N in (1024, 2048, 4096, 8192):
        # A = I + r J^m  (J = down-shift); smallest singular value via sparse-free approach:
        # A is bidiagonal-in-blocks; use svd on the banded matrix implicitly via dense for N<=8192? 
        # cheaper: smallest singular value of A equals 1/||A^{-1}|| when invertible; A is lower
        # triangular banded with unit diagonal -> solve A x = e_k costs O(N); ||A^{-1}|| approx via
        # power iteration on A^{-1} A^{-T}.
        rng = np.random.default_rng(5)
        x = rng.standard_normal(N)
        def solveA(b):      # A y = b, A = I + r J^m lower triangular
            y = b.copy()
            for i in range(m, N):
                y[i] -= r * y[i - m]
            return y
        def solveAT(b):     # A^T y = b, upper triangular
            y = b.copy()
            for i in range(N - m - 1, -1, -1):
                y[i] -= r * y[i + m]
            return y
        s = 0.0
        for _ in range(120):
            x = x / np.linalg.norm(x)
            y = solveAT(solveA(x))
            s = np.dot(x, y)
            x = y
        smin = 1.0 / np.sqrt(s)   # smallest singular value of A
        row.append(smin)
    print(f"beta={beta:4.2f} r={r:6.4f}  smin(N=1k,2k,4k,8k) = " +
          " ".join(f"{v:.5f}" for v in row))

# kernel-vector frequency at the critical weight: the near-null vector of A at r=1
N = 8192; r = 1.0
A_solve_iters = 400
rng = np.random.default_rng(7)
x = rng.standard_normal(N)
def solveA(b, r=r):
    y = b.copy()
    for i in range(m, N):
        y[i] -= r * y[i - m]
    return y
def solveAT(b, r=r):
    y = b.copy()
    for i in range(N - m - 1, -1, -1):
        y[i] -= r * y[i + m]
    return y
for _ in range(A_solve_iters):
    x /= np.linalg.norm(x)
    x = solveAT(solveA(x))
x /= np.linalg.norm(x)
# dominant frequency of x in units of cells: expect period 2m (alternating m-blocks)
X = np.abs(np.fft.rfft(x))
kmax = int(np.argmax(X[1:]) + 1)
period_cells = N / kmax
print(f"near-kernel vector dominant period = {period_cells:.1f} cells (predicted 2m = {2*m});"
      f" ordinate = pi/log2 = {np.pi/np.log(2):.4f} vs measured {np.pi/(period_cells/(2*m))/np.log(2)*1.0:.4f}"
      f" (ratio to prediction {period_cells/(2*m):.4f})")

# Bohr almost-zero driver: min |zeta(0.9+it)| on t <= 300 (full operator's denseness mechanism)
import mpmath as mp
mp.mp.dps = 20
best = (1e9, 0)
t = 0.5
while t < 300:
    v = abs(mp.zeta(mp.mpc(0.9, t)))
    if v < best[0]:
        best = (float(v), t)
    t += 0.25
print(f"min |zeta(0.9+it)| for t<=300 (grid 0.25): {best[0]:.4f} at t~{best[1]:.2f}"
      f"  (|zeta| has inf 0 on every strip line by Bohr; sections of the full weighted"
      f" operator degenerate correspondingly, RH or not)")
