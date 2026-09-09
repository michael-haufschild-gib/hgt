# SQB native spectral concentration and forcing normalization

Status: dependency-closed paper proof and Lean audit complete.
RH remains unproved. The frontier map is read-only.

## Continuous approximate kernels

Let B be a bounded self-adjoint operator on a complex Hilbert space, and let
f and g be real continuous functions on its compact real spectrum S. Suppose
every spectral zero of f is a zero of g. Define

`r_n(x)=g(x)/(1+n f(x)^2)`,

`k_n(x)=n g(x) f(x)/(1+n f(x)^2)`.

The continuous nonnegative functions |r_n| decrease pointwise to zero on S:
if f(x)=0, the zero-set condition gives g(x)=0; otherwise the denominator
tends to infinity. Dini convergence is uniform. Functional calculus therefore
gives `||r_n(B)||→0` and the exact identity

`g(B)−k_n(B)f(B)=r_n(B)`.

For any ε>0 there is a continuous factor k with operator-norm error below ε.
If `||v_i||≤M` and `||f(B)v_i||→0`, the resulting inequality

`||g(B)v_i|| ≤ ε M + ||k(B)|| ||f(B)v_i||`

proves `||g(B)v_i||→0`. Equal spectral zero sets give the converse as well.
Applied to f−c and x−b, a singleton spectral fibre `f(x)=c iff x=b` gives
equivalence of the two approximate eigen-equations for every bounded family.
There is no spectral-gap, differentiability, bounded-quotient, or spectral
membership assumption at b.

Lean: `GaloisForLFunctions.HTGeometry.CfcApproximateKernel` (4 public declarations).

## Recovery in the original modular operator

Use the original native Hilbert space, `A=1−Delta_H`, covariance `B=A^(-1)`,
entire covariance `C=g(B)`, and actual graph operator `T=C^(-1)−2`. For an
actual Xi copy q with zero rho, put

`a=5/4+(Im rho)^2/4`, `b=a^(-1)`, `c=g(b)`,

`mu=F((rho/2)(1−rho/2))`.

The previously proved exact fibre law gives `g(x)=c iff x=b` on the
nonnegative native spectrum, including its accumulation point zero. The
continuous approximate-kernel theorem now gives, for every bounded v_n,

`||(C−c)v_n||→0 iff ||(B−b)v_n||→0`.

Suppose u_n are actual T-domain unit vectors and `||(T−mu)u_n||→0`.
Self-adjointness bounds every residual below by |Im mu|. The original form
bound `T≥−1`, tested against each unit vector and estimated by Cauchy–Schwarz,
bounds it below by `−1−Re mu`. Thus mu is real and at least −1. The full-strip
classifier, using the original Xi real and imaginary parts, forces
`Re rho=1/2`. It also identifies `c(2+mu)=1`.

The actual inverse equation `C(T+2)u=u` now gives

`Cu_n−c u_n = −c C((T−mu)u_n)`.

Its norm tends to zero, so native covariance concentration follows. Define

`w_n=B u_n/||B u_n||`.

Injectivity of B proves every denominator positive. These are actual A-domain
unit vectors, since the covariance range is precisely that domain. Covariance
concentration and unit norm give `||B u_n||→b>0`. The exact native equation is

`(A−a)B u_n=−a(Bu_n−b u_n)`.

Consequently `||(A−a)w_n||→0`. Expanding w_n−u_n into a scaled covariance
residual and a scalar normalization error also proves `||w_n−u_n||→0`.
The construction preserves the original candidate family in norm. It does
not provide the assumed entire approximate family independently.

Lean: `RHTower.SelbergScatteringSpectralConcentration` (14 public declarations).

## Actual unit forcings with disappearing responses

The original pre-divisor cusp construction supplies actual A-domain unit
vectors p(t,m) with covariance residual tending to zero at
`b_t=(5/4+t^2)^(-1)` as m increases. For each integer n, choose m(n) from this
proved limit so that

`||B p(n,m(n))−b_n p(n,m(n))|| < 1/(n+1)`.

This is a choice from an analytic theorem, with no numerical search or data.
Set `f_n=p(n,m(n))`. Since `5/4+n^2≥n+1`, every n satisfies

`||f_n||=1`, `||B f_n||≤2/(n+1)`.

For each actual Xi q, let `e=1+(rho/2)(1−rho/2)` and `R_e=(A−e)^(-1)`.
The already proved original resolvent equation and covariance commutation give
the exact bounded factorization

`R_e f = Bf + e R_e Bf`.

Hence `||R_e f_n||→0` and `||C R_e f_n||→0`. For every complex target mu,

`||R_e f_n−(2+mu)C R_e f_n||→0`.

In particular the full Xi forcing numerator `||K_q f_n||` tends to zero for
every q. These limits are pointwise in q; no uniform bound over Xi copies is
claimed. Both inverse operators are injective, so `||C R_e f_n||` is positive
for every n despite tending to zero.

The actual unit response `U_n=C R_e f_n/||C R_e f_n||` retains the exact formula

`||(T−mu)U_n|| = ||C R_e f_n||^(-1) ||R_e f_n−(2+mu)C R_e f_n||`.

At the explicit target mu=i, self-adjointness proves this normalized residual
is at least one for every n, although its numerator tends to zero. This is a
concrete obstruction to replacing normalized occurrence by unscaled forcing
smallness. The positive survivor is the actual unit native family, quantitative
covariance bound, exact resolvent factorization, complete response limits,
nonzero denominators and exact normalized quotient. No claim is made about
the limiting normalized quotient at arbitrary actual Xi copies.

Lean: `RHTower.SelbergScatteringForcingEscape` (16 public declarations).

## Remaining proof obligation

SQB still requires an independent original-source mechanism producing
normalized full-Xi occurrence. The entire transformation preserves the required
native concentration; unscaled forcing cancellation is insufficient. Neither
the conditional recovery theorem nor the unconditional disappearing-response
family proves RH or its negation.

## Verification

All 34 public declarations passed scratch checks, source checks, individual
sole-target final builds and `#print axioms` audits. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Each new module is imported once by
its theorem-area umbrella and all declarations appear in the generated API
index. No full or umbrella build was run; no numerical result enters a proof.
The three target modules emitted no warnings. The two RHTower builds replayed
83 cached dependency warnings each.

The full formal lint invocation failed on five unrelated unwired RHTower
modules: `FokasLenellsCauchyModulation`, `FokasLenellsOperatorNormCauchy`,
`FokasLenellsOperatorNormInverse`, `FokasLenellsOperatorNormObstruction`, and
`FokasLenellsOperatorNormRegularity`. None of the three new SQB modules has a
lint error. Other-task modules were left untouched.
