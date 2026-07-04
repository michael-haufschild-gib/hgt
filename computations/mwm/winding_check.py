#!/usr/bin/env python3
"""Attack A (task #138 structural check): verify the winding formula
   Z_c((D-tau)(D-conj tau) A) = 2 * wind(F_B(R), tau)
for hyperbolic A (real roots), where B=(D-conj tau)A, D=d/dx, F_B=B'/B.
Also test the two-cluster no-go (expect Z_c=4, wind=2)."""
import numpy as np

def poly_from_roots(roots):
    return np.poly(roots)  # highest-degree first

def dmul(p):  # derivative of poly p (numpy highest-first)
    return np.polyder(p)

def apply_D_minus(p, c):  # (D - c) p = p' - c p
    dp = np.polyder(p)
    # align lengths
    L = max(len(dp), len(p))
    dp = np.concatenate([np.zeros(L-len(dp)), dp])
    pp = np.concatenate([np.zeros(L-len(p)), p])
    return dp - c*pp

def zc(p):  # number of non-real roots (im tol)
    r = np.roots(p)
    return int(np.sum(np.abs(r.imag) > 1e-7))

def winding_FB_around_tau(Broots, tau, npts=400000):
    # F_B(x) = sum 1/(x - rho_j); curve over x real; winding around tau
    xs = np.linspace(-60, 60, npts)
    F = np.zeros(npts, dtype=complex)
    for rho in Broots:
        F += 1.0/(xs - rho)
    # winding number of closed curve (F(-inf)=F(inf)=0) around tau
    ang = np.angle(F - tau)
    dang = np.diff(ang)
    dang = (dang + np.pi) % (2*np.pi) - np.pi  # unwrap step
    total = np.sum(dang)
    # close the curve through 0 (endpoints both ~0): add arc from F(end) to F(start) around... 
    # since F(-inf)=F(inf)=0, curve is closed; winding = total/2pi
    return total/(2*np.pi)

def test(Aroots, tau, label):
    A = poly_from_roots(Aroots)
    B = apply_D_minus(A, np.conjugate(tau))
    J = apply_D_minus(B, tau)
    Broots = np.roots(B)
    z = zc(J)
    w = winding_FB_around_tau(Broots, tau)
    imB = np.min(Broots.imag)  # UHP stability check (should be >~0 for simple A)
    print(f"{label}: deg A={len(Aroots)}, Z_c(J)={z}, 2*wind={2*w:.3f}  "
          f"[match={'YES' if abs(z-2*w)<0.05 else 'NO'}]  min Im(B-roots)={imB:.4f}")
    return z, 2*w

print("=== single-cluster (one-sided-far, expect Z_c=2, wind=1) ===")
test([-3,-2,-1,0,1,2,3], 1j, "sym cubic-ish, tau=i")
test([1,2,3,4,5], 0.3+1.2j, "one-sided g, tau=0.3+1.2i")
test([-5,-4,-3,-2,-1], 2.0+0.8j, "far one-sided, tau=2+0.8i")
test([0,1,2,3,4,5,6,7], 1j, "8 roots one-sided-ish tau=i")
print("=== two-cluster no-go (expect Z_c=4, wind=2) ===")
K=40.0
test([0,0,K,K], 1j, "y^2(y-K)^2, K=40, tau=i")
test([-30,-30.5,30,30.5], 1j, "two far pairs tau=i")
print("=== stress: tau high (b large) ===")
test([-3,-2,-1,0,1,2,3], 0+8j, "tau=8i (b large)")
test([-3,-2,-1,0,1,2,3], 0+0.2j, "tau=0.2i (b small)")
