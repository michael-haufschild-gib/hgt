#!/usr/bin/env python3
"""Doc 73 §3: sharp Chebyshev-Markov (Christoffel) certified tails from the
exact moment ladder of ReP_X (see effm_moments.py). P(X<=-a) <= 1/K_n(-a)."""
import numpy as np, math
m = {0:1.0, 2:1.0097, 4:2.8888, 6:13.0917, 8:79.3353, 10:592.8849, 12:5212.4003}
mom = [m[0],0,m[2],0,m[4],0,m[6],0,m[8],0,m[10],0,m[12]]
def christoffel_bound(a, n):
    H = np.array([[mom[i+j] for j in range(n+1)] for i in range(n+1)])
    L = np.linalg.cholesky(H)
    invL = np.linalg.inv(L)
    vals = invL @ np.array([(-a)**k for k in range(n+1)])
    return 1.0/(vals**2).sum()
for a in (3.6,4.1,4.6,5.1):
    print(f"a={a}: " + "  ".join(f"deg{2*n}: {christoffel_bound(a,n):.3e}" for n in (3,4,5,6))
          + f"   Gauss: {0.5*math.erfc(a/math.sqrt(1.0097)/math.sqrt(2)):.3e}")
