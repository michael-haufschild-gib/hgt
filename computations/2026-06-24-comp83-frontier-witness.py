"""
comp83: Verify the polynomial ODE for sin(1/(1-z)) and check boundary behavior.
Motivation: does f=sin(1/(1-z)) witness "f∈H^∞ + DA + natural boundary" (frontier of ade-boundary theorem)?
Conclusion: NO — it has only a single essential singularity at z=1, not a full natural boundary at ∂D.
ODE verified: ((1-z)^4 * f'' + f)^2 = 4*(1-f^2)*(1-z)^2.
"""
import cmath, math

def f(z):
    return cmath.sin(1/(1-z))

def df(z, h=1e-7):
    return (f(z+h) - f(z-h)) / (2*h)

def d2f(z, h=1e-5):
    return (f(z+h) - 2*f(z) + f(z-h)) / h**2

def ode_lhs(z):
    fv = f(z); f2v = d2f(z)
    return ((1-z)**4 * f2v + fv)**2

def ode_rhs(z):
    fv = f(z)
    return 4 * (1 - fv**2) * (1-z)**2

print("=== ODE verification: ((1-z)^4*f'' + f)^2 = 4*(1-f^2)*(1-z)^2 ===")
test_pts = [0.0, 0.3+0.2j, -0.5, 0.1+0.6j, 0.4-0.3j]
for z in test_pts:
    lhs = ode_lhs(z)
    rhs = ode_rhs(z)
    err = abs(lhs - rhs)
    print(f"  z={z:+.2f}  LHS={lhs:.6f}  RHS={rhs:.6f}  err={err:.2e}")

print()
print("=== Boundary approach: |f(r*exp(i*theta))| as r->0.99 ===")
import cmath
for theta_deg in range(0, 360, 30):
    theta = math.radians(theta_deg)
    z = 0.99 * cmath.exp(1j * theta)
    fval = abs(f(z))
    # also compute |f''| at these points (secret: checking jet boundedness)
    f2 = abs(d2f(z))
    print(f"  theta={theta_deg:3d}deg  z={z:.3f}  |f|={fval:.4f}  |f''|={f2:.3f}")

print()
print("=== Approach to z=1 (essential singularity): oscillates, stays bounded ===")
for r in [0.9, 0.95, 0.99, 0.999]:
    z = r * 1.0  # real axis -> z=1
    fval = f(z)
    print(f"  r={r}  f(r)={fval:.6f}  |f(r)|={abs(fval):.6f}")
