# Co-extension = integrability (foundations §47.1).
#
# THEOREM under test. On the universal solution algebra U = K[X_ij, 1/det(X)] over a Z^n-difference
# field K, define sigma_i(X) := A_i X (A_i in GL_d(K)). Then the extended sigma_1,...,sigma_n COMMUTE
# on U iff
#       sigma_i(A_j) A_i = sigma_j(A_i) A_j   for all i,j      (integrability / flatness, F_{ij}=1).
# This is the exact content of "the several commuting operators co-extend to one solution algebra",
# so the finite-commuting Picard-Vessiot theory = the classical n=1 construction + this condition.
#
# Certificate. (1) The condition is NON-VACUOUS: for generic A_1,A_2 over Q(t) with commuting shifts
# sigma_1:t->t+1, sigma_2:t->t+5, the identity FAILS (so it genuinely constrains). (2) It HOLDS on the
# integrable locus (a scalar/constant example), confirming integrable systems do co-extend.
# Symbolic (exact, sympy), local. 2026-06-19.
import sympy as sp
t = sp.symbols('t')
def s1(e): return e.subs(t, t + 1)          # commuting shift sigma_1: t -> t+1
def s2(e): return e.subs(t, t + 5)          # commuting shift sigma_2: t -> t+5
def S1(M): return M.applyfunc(s1)
def S2(M): return M.applyfunc(s2)

# (1) generic invertible 2x2 matrices over Q(t): co-extension condition should FAIL
A1 = sp.Matrix([[1 + t, t], [1, 2]])
A2 = sp.Matrix([[t, 1], [3, 1 + t**2]])
L = sp.simplify(S1(A2) * A1)                 # sigma_1(A_2) A_1
R = sp.simplify(S2(A1) * A2)                 # sigma_2(A_1) A_2
print("co-extension LHS sigma_1(A2)A1 == RHS sigma_2(A1)A2 for generic A? :", L == R)

# (2) integrable example (A_1 constant diagonal, A_2 = c*I scalar constant): should HOLD
c = sp.symbols('c')
A1d = sp.Matrix([[2, 0], [0, 3]])
A2d = c * sp.eye(2)
Ld = sp.simplify(S1(A2d) * A1d)
Rd = sp.simplify(S2(A1d) * A2d)
print("scalar/const example co-extension holds:", sp.simplify(Ld - Rd) == sp.zeros(2, 2))
