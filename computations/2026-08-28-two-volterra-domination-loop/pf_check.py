import numpy as np
N, m, r = 2048, 64, 1.0
A = np.eye(N)
for i in range(m, N):
    A[i, i - m] = r
U, S, Vt = np.linalg.svd(A)
print("smin =", S[-1], " next:", S[-2], S[-3])
v = Vt[-1]      # right singular vector for smin
u = U[:, -1]
for name, vec in (("right", v), ("left", u)):
    X = np.abs(np.fft.rfft(vec))
    k = int(np.argmax(X[1:]) + 1)
    print(f"{name} min-singular vector: dominant period {N/k:.1f} cells "
          f"(2m = {2*m}); top5 bins {np.argsort(X[1:])[-5:]+1}")
# profile check: is it a slow envelope times stride-m alternation?
blocks = v.reshape(-1, m).mean(axis=1)
print("block means sign pattern (first 12):", np.sign(blocks[:12]).astype(int))
print("envelope |block means| (every 4th):", np.round(np.abs(blocks[::4]), 4)[:8])
