"""Smoke test against independent reference values before the long runs."""
import sys
import mpmath as mp
sys.path.insert(0, ".")
import theta_common as tc

mp.mp.dps = 40

# 1. integral of Phi over R should equal 2*xi(1/2)  (bilateral Laplace at 0;
#    corpus Phi = 2 * classical Phi)
I = mp.quad(lambda x: tc.phi_derivs(x, 0)[0], [-6, 0, 6])
ref = 2 * tc.xi(mp.mpf(1) / 2)
print("int Phi  =", mp.nstr(I, 20))
print("2 xi(1/2)=", mp.nstr(ref, 20), " diff:", mp.nstr(I - ref, 5))

# 2. derivative consistency: phi_derivs vs numerical diff at x=0.7 and x=-0.7
for x0 in (0.7, -0.7, 1.9):
    v = tc.phi_derivs(x0, 3)
    nd1 = mp.diff(lambda x: tc.phi_derivs(x, 0)[0], x0)
    nd2 = mp.diff(lambda x: tc.phi_derivs(x, 0)[0], x0, 2)
    print("x=", x0, "d1 diff:", mp.nstr(v[1] - nd1, 5), "d2 diff:", mp.nstr(v[2] - nd2, 5))

# 3. evenness
a = tc.phi_derivs(1.3, 2)
b = tc.phi_derivs(-1.3, 2)
print("even check:", mp.nstr(a[0] - b[0], 5), mp.nstr(a[1] + b[1], 5), mp.nstr(a[2] - b[2], 5))

# 4. C5 identities at a benign point
d = tc.c5_point(1.0, 0.8)
print("C5/P2:", mp.nstr(d["c5_over_P2"], 12), "chkA:", mp.nstr(d["chk_action"], 5),
      "chkB:", mp.nstr(d["chk_barrier"], 5), "y:", mp.nstr(d["y"], 10))

# 5. lambda_1 via zeros ~ 0.0230957089...
mp.mp.dps = 30
s = mp.mpf(0)
for k in range(1, 400):
    g = mp.im(mp.zetazero(k))
    rho = mp.mpc(mp.mpf(1) / 2, g)
    s += 2 * mp.re(1 - (1 - 1 / rho) ** 1)
print("lambda_1 (400 zeros):", mp.nstr(s, 12), " ref 0.0230957089661210...")

# 6. Bezoutian 2x2 at simple nodes: PSD expected
mp.mp.dps = 50
nodes = [mp.mpc(1.0, 3.0), mp.mpc(0.8, -2.0)]
M = tc.bezoutian_matrix(nodes)
lo, hi, ev = tc.hermitian_min_max_eig(M)
print("bez 2x2 eigs:", [mp.nstr(e, 8) for e in ev])
print("hermitian check:", mp.nstr(abs(M[0, 1] - mp.conj(M[1, 0])), 5))
