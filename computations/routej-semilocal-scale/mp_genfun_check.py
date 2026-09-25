#!/usr/bin/env python3
"""Check the Meixner-Pollaczek generating function of the boost matrix elements
   M_{mn}(t) := int p_m(s) p_n(s) e^{i t s} dmu(s)   (orthonormal p_n, dmu = normalized |Gamma(1/4+is/2)|^2 ds)
Claim (derived from the MP generating function, lambda = 1/4, phi = pi/2, x = s/2):
   sum_{m,n} A_m A_n M_{mn}(t) w^m z^n = F(w,z;t) := [(1+w^2)(1+z^2)]^{-1/4} * ( cosh( t - (i/2) L(w,z) ) )^{-1/2},
   L(w,z) = log[ (1-iw)(1-iz) / ((1+iw)(1+iz)) ],
with degree normalizations A_n fixed by the first row M_{0n}(t) = i^n c_n (cosh t)^{-1/2} tanh(t)^n.
We extract [w^m z^n] F numerically (Cauchy integrals) and compare with grid-computed M_{mn}."""
import math, cmath
import numpy as np
from scipy.special import loggamma

def grid_matrix_elements(t, N, ds=0.01, T=400.0):
    s = np.arange(-T, T + ds/2, ds)
    logw = 2*np.real(loggamma(0.25 + 0.5j*s)); logw -= logw.max()
    w = np.exp(logw)*ds
    q = [np.sqrt(w)]; q[0] = q[0]/np.sqrt(np.sum(q[0]**2))
    a = [0.0]; qprev = np.zeros_like(q[0]); qcur = q[0]; aprev = 0.0
    for n in range(N):
        tt = s*qcur - aprev*qprev; an1 = math.sqrt(float(np.sum(tt*tt))); a.append(an1)
        qprev, qcur = qcur, tt/an1; aprev = an1; q.append(qcur)
    E = np.exp(1j*t*s)
    M = np.array([[np.sum(q[m]*q[n]*E) for n in range(N+1)] for m in range(N+1)])
    return M

def F(w, z, t):
    L = cmath.log((1-1j*w)*(1-1j*z)/((1+1j*w)*(1+1j*z)))
    return ((1+w*w)*(1+z*z))**(-0.25) * (cmath.cosh(t - 0.5j*L))**(-0.5)

def coeffs(t, N, K=256, r=0.3):
    # 2D Cauchy integral on circles of radius r
    th = 2*np.pi*np.arange(K)/K
    W = r*np.exp(1j*th)
    vals = np.array([[F(w, z, t) for z in W] for w in W])
    C = np.zeros((N+1, N+1), dtype=complex)
    for m in range(N+1):
        for n in range(N+1):
            C[m, n] = np.mean(vals * np.exp(-1j*(m*th)[:,None]) * np.exp(-1j*(n*th)[None,:])) / (r**(m+n))
    return C

t = 0.7; N = 8
M = grid_matrix_elements(t, N)
C = coeffs(t, N)
cn = [math.sqrt(math.factorial(2*n))/(2**n*math.factorial(n)) for n in range(N+1)]
# calibrate A_n from the first row: A_0 A_n C-normalization: C[0,n] = A_0 A_n M[0,n]
A0 = math.sqrt(abs(C[0,0]/M[0,0]))
A = [C[0,n]/(A0*M[0,n]) if abs(M[0,n])>1e-14 else float('nan') for n in range(N+1)]
print("first row grid M_0n:", np.round(M[0,:6],6))
print("first row corpus  :", np.round([ (1j**n)*cn[n]*(math.cosh(t))**-0.5*math.tanh(t)**n for n in range(6)],6))
print("A_n from first row:", np.round(A[:6],6))
# predicted matrix elements from F with these A_n
pred = np.array([[C[m,n]/(A[m]*A[n]) for n in range(N+1)] for m in range(N+1)])
print("max |M - pred| over m,n<=8:", np.abs(M-pred).max(), " max|M|:", np.abs(M).max())
print("diag grid:", np.round(np.real(np.diag(M))[:6],6))
print("diag pred:", np.round(np.real(np.diag(pred))[:6],6))
