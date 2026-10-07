# WP03 result

**OPEN.** The bounded zeta-quotient detector is not proved.

Lean-proved bridge: for every full-cone Weil-positive λ and ε>0 there is Cε≥0
such that, simultaneously for every N∈ℕ and every t∈ℝ,

    |Σ_{n≤N} μλ(n)n^(-it)| ≤ Cε (N+1)^(1/2+ε) (2+|t|)^ε.

All inputs come from full positivity; no individual Möbius-coefficient bound
or subcritical absolute-summability premise is added. There is no exceptional
height set. The t=0 specialization gives ordinary square-root cancellation.
A cutoff of width 1/2
agrees with the sharp integer sum exactly, and fractional Mellin decay pays
the narrowing cost. This strengthens the located smooth-sum corpus statement.

The ordinary reciprocal Dirichlet series converges at every s with Re s>1/2
and equals the same literal holomorphic reciprocal G. At s=1 its ordinary
harmonic sum is zero. These consequences are formalized in the same leaf:
`WeilWorkSingularArithmeticSharpReciprocal.lean`.

The targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal`
passed. The final direct `lake env lean` leaf audit passed with no diagnostics.
All five declarations use only `propext`, `Classical.choice`, `Quot.sound`.
The leaf is wired into RHTower. Latest formal lint reports seven unrelated
unwired modules; it reports no failure for this leaf.

The quotient bridge is now formalized: for every ε>0 there is Cε≥0 with

    |Σ_{n≤N} qλ(n)| ≤ Cε (N+1)^(1/2+ε),   qλ = 1*μλ.

Its ordinary Dirichlet series converges throughout Re s>1/2. The actual
weighted zeta norm, with weight (2+|t|)^(-1-η), is integrable for every η>0
on σ∈[1/2,3], σ≠1. This supplies the quotient's fractional Mellin mass;
polynomial strip growth separately supplies the contour shift. Pole removal
uses the existing entire zeta numerator and reciprocal primitive. All inputs
are derived from full positivity and unconditional corpus theorems.

The three new leaves are `WeilWorkSingularArithmeticWeightedZeta.lean`,
`WeilWorkSingularArithmeticMellinMass.lean`, and
`WeilWorkSingularArithmeticQuotient.lean`. Their targeted `--old` builds passed.
The quotient import makes all three reachable from RHTower. All three direct
final audits passed without diagnostics. The nine-public-declaration axiom
audit passed; every declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. Latest formal lint reports nine unrelated unwired modules and
none of these leaves.

These are classical analytic bridges, not claimed significant novelty. They do
not bound the actual quotient ζG uniformly in height.

Both coefficient sequences now also have Lean-checked square mass:

    Σ_{1≤n≤N}|μλ(n)|² ≤ Cε(N+1)^(1+ε),
    Σ_{1≤n≤N}|qλ(n)|² ≤ Dε(N+1)^(1+ε).

The reciprocal estimate follows by integrating the finite all-twist polynomial
over a time interval proportional to N and applying the sharp mean-value lower
bound. Divisor Cauchy–Schwarz and an exact summatory swap give the quotient
estimate. No infinite-series mean limit or exceptional-height removal is
asserted. The new `WeilWorkSingularArithmeticSquareMass.lean` leaf passed its
targeted `--old` build and final direct `lake env lean` audit with no diagnostics.
It is wired into RHTower. Both public declarations passed the axiom audit with
only `propext`, `Classical.choice`, and `Quot.sound`.

The open detector requires uniform twisted quotient control. The precise
sufficient bound and why ordinary cancellation does not supply it are recorded
in PROOF.md. The research goal remains active and unsolved.

Lean also proves that the literal reciprocal G is unbounded on every half-plane
Re s>x with 1/2<x<1. Its unique zero at1 contradicts the zero recurrence that
a bounded Dirichlet continuation would force. This does not obstruct ζG:
the zeta pole cancels that zero. The source capstone in
`WeilWorkSingularArithmeticReciprocalObstruction.lean` passed its targeted
`--old` build, final direct audit, and standard-axiom audit. Its import is wired.
This is a classical Bohr bridge, not a new-science claim or a solution of WP03.

The actual quotient growth comparison is also fully audited and wired:
on every strip 1/2+δ≤σ≤5/2, with 0<δ<1/2, and at sufficiently large |t|,

    (|t|+3)^(-ε)|ζ(σ+it)| ≤ |ζ(σ+it)G(σ+it)|
      ≤ (|t|+3)^ε|ζ(σ+it)|.

The capstone in `WeilWorkSingularArithmeticGrowthComparison.lean` derives G
and the comparison from full positivity alone. Targeted `--old` build, final
direct audit, and standard-axiom audit passed. The comparison includes zeta
zeros. It corrects the proposed interpretation of a subpower quotient estimate:
that estimate is the corresponding zeta Lindelöf question under hW, rather
than a new cancellation mechanism. Uniform boundedness remains unproved.

The actual reciprocal now has a fully verified mean-square identity. For
the same literal G and every fixed sigma>1/2,

    lim_(T→infinity) (1/T) integral_0^T |G(sigma+it)|² dt
      = sum_(n≥1) |mu_lambda(n)|² n^(-2sigma) < infinity.

This is the actual untwisted function. Its proof includes a uniform ordinary
series tail: for every alpha>1/2 and epsilon>0, some K>=0 gives

    |G(sigma+it)-sum_(n<=N)mu_lambda(n)n^(-sigma-it)|
      <= K(2+|t|)^epsilon(N+1)^(alpha-sigma)

for every sigma>alpha, N and t. Weighted square summability is proved for
both mu_lambda and q_lambda at every sigma>1/2. The finite approximants with
N=floor(sqrt(T)) have the same limiting mean square as G.

The four leaves `WeilWorkSingularArithmeticReciprocalTail`,
`WeilWorkSingularArithmeticSquareSummability`,
`WeilWorkSingularArithmeticMeanComparison`, and
`WeilWorkSingularArithmeticReciprocalMeanSquare` passed targeted `--old`
builds and final direct `lake env lean` audits without diagnostics. All six
public capstones passed the standard-axiom audit; all imports are wired.
Latest lint names seven unrelated unreachable modules and no WP03 failure.

Classification: BRIDGE, not new scientific knowledge. The result is fixed-line
and averaged: it supplies neither a uniform bound on the actual quotient nor
uniformity at a moving critical-line distance. WP03 remains OPEN.

The forward coefficients a_lambda=dirichletExp(logZetaCoeff(truncate lambda))
now satisfy the stronger critical energy estimate

    sum_(1<=n<=N) |a_lambda(n)|^2/n <= K_lambda*(1+log N),  N>=1.

The exact signed convolution lambda0*a_lambda=(log n)*a_lambda is also
formalized. Substituting a_lambda(n)/sqrt(n) into the existing Weil--Toeplitz
ceiling gives its logarithmic-moment inequality; a finite induction proves
the bound. No sign, multiplicativity, or extra coefficient premise is added.

WeilWorkSingularArithmeticForwardCoefficients passed its targeted --old
build, final direct lake env lean audit, and all seven public-declaration
axiom checks with only propext, Classical.choice, and Quot.sound. Import is
wired. Latest lint reports16 unrelated unreachable modules, no WP03 failure.
Classification remains BRIDGE: a new formalized consequence of the source
bound, not a claimed scientific solution or uniform quotient estimate.

The finite two-prime obstruction is also classified in Lean. For the real
divisor-square form on (1,p,q,pq), put a=lambda(p)/sqrt(p),
b=lambda(q)/sqrt(q), u=sqrt(a^2+b^2). Its ceiling u holds exactly when the
composite entry is -2ab/u (zero in the degenerate case). An exact sum of
two squares proves sufficiency, and the star vector attains the ceiling.
WeilWorkSingularArithmeticDivisorCompletion passed its targeted --old build,
final direct audit, and three standard-axiom checks; import wired.

This is a classical finite completion bridge, not a full-positive source
counterexample. It rules out improving the star bound merely by adding pq.
The next candidate uses coupled prime-to-pair layers and keeps pq<=N.
Half-power exponent1/4, sharp prime variance, and the WP03 detector remain OPEN.

## Cycle27: the whole Toeplitz relaxation has sharp constant1

Lean now constructs one nonnegative, prime-supported lambda satisfying
every complex multiplicative Toeplitz test with budget log N and C=0.
At every cutoff its square mass is <=(log N)^2. Nevertheless, for every
theta<1, prime-square mass exceeds theta*(log N)^2 arbitrarily far out.

The capstone is
`WeilSingularArithmetic.exists_sharp_prime_supported_toeplitz_weight` in
`WeilWorkSingularArithmeticToeplitzSharpness.lean`. Targeted --old build,
final direct lake env lean, and all six standard-axiom checks passed.
Import is wired. Latest lint reports18 unrelated unreachable leaves;
no WP03 or forbidden-declaration failure.

This retires improving the prime-variance constant solely from the already
extracted Toeplitz ceilings. Arbitrarily complicated divisor-layer tests
and all-cutoff compatibility within that relaxation cannot suffice.
The positive survivor is an exact sharp infinite construction, not merely
the negation of the proposed bound. Its methods are classical; no claim of
publication-level novelty is made. This is not a full-positive source or
a detector counterexample. The full-source conjecture and WP03 stay OPEN.

## Cycle29: sharp source sums and ordinary harmonic convergence

For every full-positive source, with lambda0 truncated below2, Lean now proves

    |sum_(n<=N) lambda0(n)-N| <= C_epsilon*(N+1)^(1/2+epsilon).

It also proves ordinary Dirichlet convergence of lambda0(n)-1 throughout
Re s>1/2, and existence of the ordinary real limit

    lim_N sum_(n<=N) (lambda0(n)-Lambda(n))/n.

No nonnegativity, pointwise coefficient bound, local-mass, or Tauberian
premise is added to full positivity. The integer-gap Perron proof removes
the pole explicitly and shifts the source's holomorphic regular part.

The leaves `WeilWorkSingularArithmeticPolePerron.lean` and
`WeilWorkSingularArithmeticSummatory.lean` passed targeted --old builds,
final direct lake env lean checks, and all five standard-axiom audits.
Imports are wired. Lint reports eight unrelated unreachable leaves and no
WP03 or forbidden-declaration failure; index refresh passed.

Classification: BRIDGE. This removes the extra local-mass premise for
ordinary harmonic convergence. It does not prove the limit's sign,
absolute local-mass control, or the uniform quotient bound. WP03 is OPEN.

## Cycle30a: the actual positive Gaussian source pairing

For every full-positive source, let Phi be its existing Herglotz continuation
and b_T(s)=zeta(s)*zeta(1-s)*exp((s-1/2)^2/T^2). For every T>=1, the new
pairing leaves prove absolute integrability and the exact identity

    Re integral_R Phi(3/4+it)*b_T(3/4+it) dt
      = pi * integral_R |zeta(1/2+ir)|^2 exp(-r^2/T^2) dmu_lambda(r)
      >= 0.

Every test hypothesis is discharged for this concrete b_T. There is no added
boundary regularity, total-mass finiteness, coefficient-size or NotchSmall
premise. The proof keeps the regularized Herglotz kernel intact through
Fubini, using the source's existing weighted-finite positive measure.

Targeted --old builds passed for CauchyReflection, HerglotzPairing and
GaussianPairing under the WeilWorkSingularArithmetic prefix. Umbrella imports
are wired. All three final direct source checks passed without warnings;
five axiom audits report only propext, Classical.choice and Quot.sound.
Global lint reports eight unrelated unreachable modules, no owned failure
and no forbidden declaration.

Classification: BRIDGE, no publication novelty claim. This closes C30's
positive-boundary-pairing obligation. The canonical contour subtraction,
signed Gaussian coefficient extraction, Mellin main term and final harmonic
sign remain unformalized. The uniform quotient goal WP03 remains OPEN.
