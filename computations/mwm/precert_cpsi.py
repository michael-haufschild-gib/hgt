#!/usr/bin/env python3
"""Pre-certify the C_psi frame gap (doc 41 (K3), task #147 item (c)).

Frames (theta = 1/2, xi in [1/i, 1]):
  log:  v = c log(1+xi),                u = -c log(1-xi)
  psi:  v = c(psi(i(1+xi)+1)-psi(i+1)), u = c(psi(i+1)-psi(i(1-xi)+1))
Integrand (weights EXACT in both frames, doc 40 SS1):
  Psi(xi) = c xi [ w(v)/(1+xi) - w(u)/(1-xi) ],  w(x) = csch^2(x/2)/2.
Claims:
  (1) gap := int Psi_psi - int Psi_log  scales as C/i, |C| <= 6;
  (2) shift formulas: Dv ~ -(c/2) xi/(i(1+xi)), Du ~ -(c/2) xi/(i(1-xi));
  (3) split sizes: common O(xi/i) hits cancelling bracket O(1/(c^2 xi)),
      asym Dv-Du ~ (c/i) xi^2/(1-xi^2) hits non-cancelling O(1/(c^2 xi^2)).
"""
from mpmath import mp, mpf, csch, log, exp, quad, digamma

mp.dps = 40

def w(x):
    return csch(x / 2) ** 2 / 2

def psi_frame_gap(c, i, xiA=1):
    c, i = mpf(c), mpf(i)
    lo, hi = 1 / i, mpf(xiA)

    def integrand_log(xi):
        v = c * log(1 + xi)
        u = -c * log(1 - xi) if xi < 1 else None
        if xi >= 1:
            return c * xi * w(v) / (1 + xi)
        return c * xi * (w(v) / (1 + xi) - w(u) / (1 - xi))

    def integrand_psi(xi):
        v = c * (digamma(i * (1 + xi) + 1) - digamma(i + 1))
        u = c * (digamma(i + 1) - digamma(i * (1 - xi) + 1))
        if xi >= 1:
            return c * xi * w(v) / (1 + xi)
        return c * xi * (w(v) / (1 + xi) - w(u) / (1 - xi))

    # split at 1/2 and near the endpoint for quadrature stability
    pts = [lo, mpf('0.5'), mpf('0.9'), hi - 1 / (2 * i), hi]
    Ilog = quad(integrand_log, pts)
    Ipsi = quad(integrand_psi, pts)
    return Ipsi - Ilog

print(f"{'c':>5} {'i':>6} {'gap':>15} {'gap*i':>10}")
for c in [2, 2.5, 4, 6]:
    for i in [100, 200, 500, 1000]:
        g = psi_frame_gap(c, i)
        print(f"{c:5} {i:6} {float(g):15.3e} {float(g * i):10.4f}")

# (2) shift formula check at c=2, i=200
c, i = mpf(2), mpf(200)
print("\nshift check (c=2, i=200): xi, Dv_true, Dv_model, Du_true, Du_model")
for xi in [mpf('0.05'), mpf('0.2'), mpf('0.5'), mpf('0.9')]:
    Dv = c * (digamma(i * (1 + xi) + 1) - digamma(i + 1)) - c * log(1 + xi)
    Du = c * (digamma(i + 1) - digamma(i * (1 - xi) + 1)) - (-c * log(1 - xi))
    Dvm = -(c / 2) * xi / (i * (1 + xi))
    Dum = -(c / 2) * xi / (i * (1 - xi))
    print(f"  {float(xi):4.2f} {float(Dv):11.3e} {float(Dvm):11.3e} "
          f"{float(Du):11.3e} {float(Dum):11.3e}")
