#!/usr/bin/env python3
"""MUST-171: the bilinear (eps1 eps2) response of log D_n for the two-mode weight
   w (1 + 2 eps1 cos(d1 s)) (1 + 2 eps2 cos(d2 s)).
 Exact formula (covariance of linear statistics):  B_n = tr T(d1+d2) + tr T(d1-d2) - tr(T(d1) T(d2)),
 T(d)_{ij} = 2 int p_i p_j cos(d s) dmu  (orthonormal archimedean Jacobi basis, indices 0..n).
 (1) check B_n against a finite-difference mixed derivative of log det Gram (small n).
 (2) sizes for d1 = log p1, d2 = log p2: beat term 2 sum m_i(d1-d2), sum-mode term, truncation defect
     4 sum_{i,j<=n} Re M_ij(d1) Re M_ij(d2); and the radius-level second differences."""
import numpy as np, math, sys
from scipy.special import loggamma

def basis(nmax, T, ds):
    s = np.arange(-T, T + ds/2, ds)
    logw = 2*np.real(loggamma(0.25 + 0.5j*s)); logw -= logw.max()
    w = np.exp(logw)*ds; w /= w.sum()          # probability weights
    q = np.zeros((nmax+1, len(s)))
    q[0] = np.sqrt(w)
    r = lambda n: math.sqrt((n+0.5)*(n+1))
    q[1] = s*q[0]/r(0)
    for n in range(1, nmax):
        q[n+1] = (s*q[n] - r(n-1)*q[n-1])/r(n)
    return s, w, q     # q[n] = p_n sqrt(w)  (orthonormal on the grid)

def tangent(q, s, d):    # T(d)_{ij} = 2 sum_s q_i q_j cos(d s)
    return 2*(q*np.cos(d*s)) @ q.T

def boostRe(q, s, d):    # Re M_ij(d) = sum q_i q_j cos(d s)
    return (q*np.cos(d*s)) @ q.T

def logdet_gram(q, s, d1, d2, e1, e2):
    f = (1 + 2*e1*np.cos(d1*s))*(1 + 2*e2*np.cos(d2*s))
    G = (q*f) @ q.T
    return np.linalg.slogdet(G)[1]

nmax = 12; T = 2.2*nmax + 80; ds = 0.005
s, w, q = basis(nmax, T, ds)
print("orthonormality error:", np.abs(q @ q.T - np.eye(nmax+1)).max())
d1, d2 = math.log(7.0), math.log(3.0)
for n in (3, 8, 12):
    qn = q[:n+1]
    B = np.trace(tangent(qn, s, d1+d2)) + np.trace(tangent(qn, s, d1-d2)) - np.trace(tangent(qn, s, d1) @ tangent(qn, s, d2))
    e = 1e-3
    fd = (logdet_gram(qn, s, d1, d2, e, e) - logdet_gram(qn, s, d1, d2, e, -e) - logdet_gram(qn, s, d1, d2, -e, e) + logdet_gram(qn, s, d1, d2, -e, -e))/(4*e**2)
    print("(1) n=%d  B_n=%.10f  finite-difference=%.10f  diff=%.2e" % (n, B, fd, B-fd))

# (2) sizes for a real prime pair
p1, p2 = 211, 421
d1, d2 = math.log(p1), math.log(p2); eps = (p1*p2)**-0.5
nmax = 160; T = 2.2*nmax + 80; ds = 0.004
s, w, q = basis(nmax, T, ds)
print("orthonormality error (nmax=%d):" % nmax, np.abs(q @ q.T - np.eye(nmax+1)).max())
Rm = boostRe(q, s, d1); Rp = boostRe(q, s, d2)
mminus = np.array([2*np.sum(q[i]**2*np.cos((d1-d2)*s)) for i in range(nmax+1)])   # 2 m_i(d1-d2)
mplus = np.array([2*np.sum(q[i]**2*np.cos((d1+d2)*s)) for i in range(nmax+1)])
Bn = []; beat = []
for n in range(nmax+1):
    defect = 4*np.sum(Rm[:n+1, :n+1]*Rp[:n+1, :n+1])
    bt = mminus[:n+1].sum(); sm = mplus[:n+1].sum()
    Bn.append(bt + sm - defect); beat.append(bt)
    if n in (10, 20, 40, 60, 80, 100, 120, 150):
        print("(2) n=%d  beat=2sum m(d-)=%.6f  sum-mode=%.3e  defect=%.3e  B_n=%.6f  (B_n-beat)/beat=%.2e  eps*n=%.3f  bound 64(2n+1)eps=%.2f  |M|max=%.2e  (cosh d1 cosh d2)^-1/2=%.2e" %
              (n, bt, sm, defect, Bn[-1], (Bn[-1]-bt)/bt, eps*n, 64*(2*n+1)*eps, np.abs(Rm[:n+1,:n+1]).max(), (math.cosh(d1)*math.cosh(d2))**-0.5))
Bn = np.array(Bn); beat = np.array(beat)
# radius level: L12(n) = B_{n+1} - 2B_n + B_{n-1} vs beat jet 2(m_{n+1}(d-) - m_n(d-)) ; and the product of first-order jets
mm1 = np.array([2*np.sum(q[i]**2*np.cos(d1*s)) for i in range(nmax+1)]); mm2 = np.array([2*np.sum(q[i]**2*np.cos(d2*s)) for i in range(nmax+1)])
for n in (10, 20, 40, 60, 80, 100, 120, 150):
    L12 = Bn[n+1] - 2*Bn[n] + Bn[n-1]; Lbeat = beat[n+1] - 2*beat[n] + beat[n-1]
    prod = (mm1[n+1]-mm1[n])*(mm2[n+1]-mm2[n])/4   # (1/4) L1 L2 with L_a = 2(m_{n+1}-m_n)
    dS = lambda m: 4*(np.sum(Rm[:m+1,:m+1]*Rp[:m+1,:m+1]) - np.sum(Rm[:m,:m]*Rp[:m,:m]))
    print("(3) n=%d  L12=%.4e  beat-jet=%.4e  rel diff=%.2e  L1L2/4=%.2e  |dS_n|=%.2e  |dS_{n+1}-dS_n|=%.2e  eps*sqrt(n)=%.3f" % (n, L12, Lbeat, (L12-Lbeat)/Lbeat, prod, abs(dS(n)), abs(dS(n+1)-dS(n)), eps*math.sqrt(n)))
