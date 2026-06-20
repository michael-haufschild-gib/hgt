import mpmath as mp

mp.mp.dps = 60

TOL = mp.mpf("1e-50")

def relerr(a, b):
    scale = max(mp.mpf(1), abs(a), abs(b))
    return abs(a - b) / scale

def assert_close(label, lhs, rhs, tol=TOL):
    err = relerr(lhs, rhs)
    print(f"{label}:")
    print(f"  lhs       = {mp.nstr(lhs, 40)}")
    print(f"  rhs       = {mp.nstr(rhs, 40)}")
    print(f"  rel.err   = {mp.nstr(err, 6)}")
    assert err < tol, f"{label} failed with relative error {err}"

print("=" * 72)
print("HYPERTRANSCENDENTAL VALUE-CONSTRAINT TEST: Gamma reflection formula")
print("=" * 72)
print()
print("Constraint: Gamma(z) * Gamma(1-z) = pi / sin(pi*z)")
print("This checks an equality of values of a hypertranscendental function.")
print()

test_points = [
    mp.mpf("0.125"),
    mp.mpf("0.2"),
    mp.mpf("0.33333333333333333333333333333333333333333333333333"),
    mp.mpf("0.7"),
    mp.mpf("-1.375"),
    mp.mpc("0.4", "0.3"),
    mp.mpc("-0.6", "0.8"),
]

for z in test_points:
    lhs = mp.gamma(z) * mp.gamma(1 - z)
    rhs = mp.pi / mp.sin(mp.pi * z)
    assert_close(f"z = {mp.nstr(z, 20)}", lhs, rhs)
    print()

print("=" * 72)
print("SECOND VALUE-CONSTRAINT TEST: Gamma multiplication formula, n=3")
print("=" * 72)
print()
print("Constraint: Gamma(z) Gamma(z+1/3) Gamma(z+2/3)")
print("          = 2*pi * 3^(1/2-3z) * Gamma(3z)")
print()

for z in [mp.mpf("0.4"), mp.mpf("1.1"), mp.mpf("2.25"), mp.mpc("0.75", "0.2")]:
    lhs = mp.gamma(z) * mp.gamma(z + mp.mpf(1) / 3) * mp.gamma(z + mp.mpf(2) / 3)
    rhs = 2 * mp.pi * mp.power(3, mp.mpf("0.5") - 3 * z) * mp.gamma(3 * z)
    assert_close(f"z = {mp.nstr(z, 20)}", lhs, rhs)
    print()

print("VERDICT: all hypertranscendental Gamma value constraints passed.")
