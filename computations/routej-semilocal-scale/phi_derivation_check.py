#!/usr/bin/env python3
"""Checks of the derivation of Phi:
 (1) diagonal cosine moments m_n(t) = (cosh t)^{-1/2} 2F1(-n, n+1/2; 1; tanh^2 t) = (cosh t)^{-1/2} P_n^{(0,-1/2)}(1 - 2 tanh^2 t)
     against grid values;
 (2) generating function sum c_m c_n M_mn w^m z^n = (cosh t)^{-1/2} (1 - w z - i tanh t (w+z))^{-1/2};
 (3) Phi_derived(x) = 4 sqrt(2/pi) [ sqrt(x) cos(4x) - 8 x^{3/2} sin(4x) ] against the collapse profile."""
import json, math, cmath
import numpy as np
from scipy.special import loggamma, eval_jacobi, hyp2f1
from mp_genfun_check import grid_matrix_elements, coeffs

t = 0.7; N = 8
M = grid_matrix_elements(t, N)
cn = [math.sqrt(math.factorial(2*n))/(2**n*math.factorial(n)) for n in range(N+1)]
phi = math.cosh(t)**-0.5; tau2 = math.tanh(t)**2
print("(1) diagonal: grid vs 2F1 vs Jacobi P_n^{(0,-1/2)}(1-2 tanh^2)")
for n in range(N+1):
    print("  n=%d grid=%+.8f  2F1=%+.8f  jacobi=%+.8f"%(n, M[n,n].real, phi*hyp2f1(-n, n+0.5, 1.0, tau2), phi*eval_jacobi(n, 0.0, -0.5, 1-2*tau2)))
# (2) corrected generating function
def F2(w, z, t):
    return (math.cosh(t))**-0.5 * (1 - w*z - 1j*math.tanh(t)*(w+z))**-0.5
K = 256; r = 0.3; th = 2*np.pi*np.arange(K)/K; W = r*np.exp(1j*th)
vals = np.array([[F2(w, z, t) for z in W] for w in W])
C = np.zeros((N+1,N+1), dtype=complex)
for m in range(N+1):
    for n in range(N+1):
        C[m,n] = np.mean(vals*np.exp(-1j*(m*th)[:,None])*np.exp(-1j*(n*th)[None,:]))/(r**(m+n))
pred = np.array([[C[m,n]/(cn[m]*cn[n]) for n in range(N+1)] for m in range(N+1)])
print("(2) generating function: max |M - pred| =", float(np.abs(M-pred).max()), " (max|M| = %.3f)"%float(np.abs(M).max()))
# (3) Phi
r = json.load(open("routej_collapse.json")); rows = {row["p"]: row for row in r}
def Phi_der(x): return 4*math.sqrt(2/math.pi)*(math.sqrt(x)*math.cos(4*x) - 8*x**1.5*math.sin(4*x))
for p in (1009, 1511):
    D = np.array(rows[p]["D_all"]); ks = np.arange(1, len(D)+1); x = 2*ks/p; Phi = math.sqrt(p)*D
    m = (x >= 0.3) & (x <= 2.3)
    der = np.array([Phi_der(xx) for xx in x[m]])
    print("(3) p=%d: rms(Phi - Phi_derived)=%.3f  rms(Phi)=%.2f  rel=%.4f ; samples:"%(p, math.sqrt(np.mean((Phi[m]-der)**2)), math.sqrt(np.mean(Phi[m]**2)), math.sqrt(np.mean((Phi[m]-der)**2)/np.mean(Phi[m]**2))))
    for xv in (0.3, 0.6, 0.823, 1.0, 1.269, 1.586, 2.024, 2.3):
        k = int(round(xv*p/2)); print("      x=%.3f Phi=%8.3f derived=%8.3f"%(xv, Phi[k-1], Phi_der(xv)))
print("Taylor coefficients of Phi_derived: c1 = 4 sqrt(2/pi) = %.4f, c3 = -160 sqrt(2/pi) = %.3f, c5 = 384 sqrt(2/pi) = %.2f"%(4*math.sqrt(2/math.pi), -160*math.sqrt(2/math.pi), 384*math.sqrt(2/math.pi)))
