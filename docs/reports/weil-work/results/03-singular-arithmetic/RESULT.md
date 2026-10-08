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
positive-boundary-pairing obligation. The remaining C30 obligations are
tracked in the continuation below. The uniform quotient goal WP03 remains OPEN.

## Cycle30b: exact source contour and sublinear arithmetic error

Let R=A-Phi, p=(s-1)zeta(s), P=R*p+p', and
F=[(A+1/(s-1)-Phi)zeta+zeta']zeta(1-s). The new leaves establish:

- Canonical contour subtraction: the real Gaussian integral of F on3/4
  equals minus pi times the actual positive boundary-measure pairing.
- Exact pole transport to3/2, retaining both the boundary mass and
  the source residue term -pi*Re(P(1))*exp(1/(4*T^2)). The common analytic
  numerator also gives (s-1)^2 V(s)->P(1) for V=(R+1/(s-1))*zeta^2+zeta'*zeta.
- Literal arithmetic extraction: for a=((lambda0-Lambda)*1)*1, L(a,s)=V(s)
  on Re s>1 and the right Gaussian contour equals2*pi*sum a(n)J_T(n).
- Absolute convergence and a norm bound C*T^(5/6) for the error series
  sum a(n)[J_T(n)-2*exp(-4*pi^2*n^2/T^2)], using only source absolute
  Dirichlet summability at9/8.

All source statements use hW alone, with T>=1 as the test parameter range.
Five targeted modules passed; all are wired into RHTower. Final direct
source checks and the warning cleanup check passed without warnings.
All37 public-declaration axiom audits use only propext, Classical.choice
and Quot.sound. Lint reports six unrelated unreachable modules, no WP03
failure or prohibited declaration. Source index refresh passed; generated
catalog files have no Git diff. No full or umbrella build was run.

Classification: BRIDGE. The signed Gaussian upper bound is recorded in
the continuation below. The one-sided Mellin argument and
identification of P(1) with the ordinary harmonic limit remain paper
obligations. Neither the full C30 sign nor WP03 is claimed complete.

## Cycle30c: the actual signed Gaussian upper bound

For every full-positive source and a=((lambda0-Lambda)*1)*1, there is C>=0
such that, for every T>=1,

    Re sum a(n)*exp(-4*pi^2*n^2/T^2) <= C*T^(5/6).

GaussianBound also proves absolute convergence of the Gaussian and kernel
series before subtracting them. Its norm bound D*T^2 for the Gaussian
series holds for every T>0 and will control the large-t Mellin tail.
No coefficient sign, local absolute-mass bound or source pole sign is
assumed. The bound follows from the exact contour and audited error series.

The targeted --old build and final direct source audit pass without
warnings. The module is wired; all four axiom reports contain only
propext, Classical.choice and Quot.sound. The index refresh passed.
Lint reports six unrelated unreachable modules, no WP03 failure.
Classification: BRIDGE. The actual Mellin transform with convergence,
the pole-limit sign, and the ordinary harmonic-limit identification remain
to be formalized. WP03 remains OPEN.

## Cycle30d: unconditional ordinary harmonic sign

For every full Weil-positive source, the ordinary sums

    sum_(n<=N) (lambda0(n)-Lambda(n))/n

converge to Re(P(1))<=0. No NotchSmall, local absolute-mass bound,
coefficient sign, pointwise regularity, zero-free statement or RH premise
is added. This removes the NotchSmall premise from the older scalar sign
theorem in WeilConeHarmonicPinning.

GaussianProfile normalizes the literal signed convolution to
Hpi(t)=sum a(n)exp(-pi*n²*t). Mellin separately proves actual absolute
integrability and the exact identity Mellin(Hpi,s/2)=Gamma_R(s)*V(s)
for Re s>1. MellinBound gives a uniform upper bound for its real part
on1<s<3/2, using a fixed integrable upper envelope. PoleSign extracts
Re(P(1))<=0. HarmonicSign identifies P(1)'s real part with the ordinary
harmonic deviation limit through centered Dirichlet continuity at1 and
the zeta Laurent constant.

All five targeted --old builds and final direct lake-env-lean source
checks pass without warnings. All12 public declarations have only
propext, Classical.choice and Quot.sound in their axiom lists. All five
imports are wired. Classification: PROGRESS/BRIDGE. The analytic Mellin
machinery is classical; no literature-novelty claim is made.

WP03 remains OPEN. A scalar nonpositive limit gives neither equality
nor uniform quotient boundedness. On 2026-10-08, C31's proposed
phase-free three-dilate identity FAILED: the kernel carries
cos(2*pi*y), hence the half-integer scale twists a(n) by (-1)^n.
There is no scalar Mellin multiplier forcing harmonic equality.
C31a's positive survivor is now formalized: exact cosine-twisted
extraction at every positive real scale, with one source constant and
error at most C*r^(-1/8)*T^(5/6). Both arithmetic series and the actual
scaled contour are integrable/summable before extraction. The half-scale
main term explicitly contains (-1)^n.

TwistedGaussianError and TwistedExtraction add nine public theorems.
Both targeted --old builds and both final direct lake-env-lean checks
pass without warnings; all nine axiom audits are standard-only. Imports
are wired. Lint reports nine unrelated unreachable modules, no WP03
error; global lint is not green. Classification: PROGRESS/BRIDGE.

C31b is now COMPLETE: for every real c and full-positive source,

    Re[(1+c^2/2)H(t) -(c/2)H_alt(t/4) -cH(4t)] <= C_c*t^(-5/12)

on0<t<=1. The half-scale parity term is retained. The proof derives
weighted spectral nonnegativity and the residue shift from hW alone;
no NotchSmall, local mass, arithmetic limit, or pole-sign premise is added.
PolynomialWeight, PolynomialPairing, PolynomialShift, PolynomialGaussian,
and PolynomialProfile all pass targeted --old and final direct source
checks without warnings. All30 public declarations have standard-only
axiom reports. All five imports are wired; no umbrella build was run.
Classification: PROGRESS/BRIDGE; no literature-novelty claim.

C32a is now COMPLETE: write ell=Re(P(1))<=0 and
b(sigma)=(sigma-1)^2 Re(Gamma_R(sigma)*V_alt(sigma)), where V_alt is
the actual absolutely convergent alternating arithmetic Dirichlet series
on Re s>1. For every epsilon>0, eventually as sigma decreases to1,

    |b(sigma)+ell/2| <= -sqrt(2)*ell+epsilon.

No twisted-pole existence or convergence premise is added. The proof
pays actual alternating Mellin convergence, the weighted transform,
absolute large-t control, and a uniform real Mellin upper bound before
using two fixed coefficients +/-sqrt(2). The interval remains nontrivial
when ell<0; convergence and equality ell=0 do not follow.

All six new leaves and the two touched Mellin leaves pass targeted --old
checks and eight final direct lake-env-lean audits with empty diagnostics.
All21 public declarations in those files have standard-only axiom reports.
Six imports wired; no full/umbrella build. Classification: PROGRESS/BRIDGE,
with no literature-novelty claim. Parent C32's full arithmetic fibre law,
ordinary twisted limits, harmonic equality and the WP03 quotient bound
remain OPEN.

C33 analytic BRIDGE is COMPLETE. For every full-positive source, one
constant D controls every finite real polynomial, every N and every T>=1:

    Re A_T(c) <= D*E(c)*(N+1)^(9/8)*T^(5/6),
    E(c)=sum_(1<=m<=N)c_m^2/m.

Consequently N+1<=T^theta gives exponent5/6+9*theta/8, sublinear for
theta<4/27. The exact all-ratio extraction, spectral pairing, residue
and both coefficient budgets are paid. No arithmetic lower bound is
proved. FiniteWeight, FiniteGaussian, FinitePairing, FiniteShift,
FiniteEnergy and FiniteBound pass all targeted --old and six final direct
source checks with empty diagnostics. All29 public declarations have
standard-only axiom reports. Six imports wired; no umbrella/full build.

C33's proposed positive order-T detector, restricted to full-positive
sources, is target-equivalent after this bound; verdict CIRCULAR as a
research proposal. The verified analytic bound survives as BRIDGE, not a
solution or literature-novel result. WP03 remains OPEN.

C34 critical absolute-harmonic rigidity was REDISCOVERED, not advanced:
WeilAbsoluteConvergenceRigidity already proves it. More strongly,
WeilOneSidedConvergenceRigidity proves either sign part summable against
1/n forces equality. Any distinct source has both sign parts divergent
at1, despite absolutely summable signed unit-log-window masses. Next
research must address that mixed cancellation, without adding tail
summability or a detection premise.


## C35a: actual forward energy and residual variance, verified 2026-10-08

For every `hW : WeilPositiveFull lam`, let `a = forwardCoeff lam` and
`B = WeilWorkSettledPhase.sourceCompletion hW 1`. There exist finite
real K>0 and V>=0 such that

    sum_(1<=n<=N) |a(n)|^2/n / log N -> K,
    sum_(1<=n<=N) |a(n)-B|^2/n / log N -> V,
    K = |B|^2 + V.

No coefficient ordering, multiplicativity, extra convergence or growth
premise is added. The actual centered harmonic sum converges, and both
coordinates of sum a(n)/n / log N converge to B. The two coefficient
definitions are explicitly identified.

The exact log-moment ceiling gives a decreasing normalized primitive;
finite secants then force the energy limit. This is a BRIDGE application
of classical monotone density, not a new Tauberian theorem or a claimed
scientific breakthrough. Parent C35 (V=0) remains OPEN. Even its connection
to the exact uniform bounded-quotient receiver still needs proof.

Entry point: `WeilWorkSingularArithmeticForwardVariance.lean:35`,
`exists_forwardCoeff_energy_variance`. Five leaves, 486 lines, 17 public
declarations. All targeted --old checks and all five final direct
`lake env lean <module>` checks PASS. Axiom audit: only propext,
Classical.choice, Quot.sound. Five umbrella imports wired; no umbrella
build. Global lint fails on six unrelated unreachable modules; no owned
or prohibited-declaration finding. See EVIDENCE for exact scope.


## C37: actual parity residue is bounded by actual variance, verified 2026-10-08

For every `hW : WeilPositiveFull lam`, let B be its actual completion at1.
There exist V>=0 and r>0, with V the actual centered logarithmic energy
limit and r the actual odd/full radial ratio, such that

    |B|^2*(2*r-1)^2 <= V.

No first-mean conclusion for odd coefficients or analytic continuation of
the odd series is assumed. An Abelian upper bound transfers the existing
variance limit to damped energy; weighted Cauchy--Schwarz bounds the
actual alternating residue. The constant is sharp for general coefficient
sequences, not asserted sharp within the full-positive cone.

Entry point: `WeilWorkSingularArithmeticParityVariance.lean:83`,
`exists_forward_parity_variance`. Three leaves,342 lines,five public
theorems. Targeted --old builds, final direct Lean checks and all five
axiom checks PASS; only propext,Classical.choice,Quot.sound. Umbrella
imports wired. Lint fails on five unrelated unwired HTGeometry leaves.
Verdict BRIDGE, not significant scientific novelty. V=0, canonical r=1/2,
and the original uniform bounded quotient remain OPEN.

## C39a: actual sieve residues vanish with the prime cutoff, verified 2026-10-08

For arbitrary `hW : WeilPositiveFull lam`, let B be its nonzero actual
forward residue and K>0 its actual logarithmic coefficient-energy limit.
For every Q>=1 the actual coprime/full radial ratio has a positive limit
r_Q, and the SAME K satisfies

    |B|^2*r_Q^2 <= K*phi(Q)/Q.

Consequently r_(primorial N)->0. The radial limit is taken first for each
fixed modulus, then the prime cutoff tends to infinity. No uniform radial
error, coefficient sign, multiplicativity, or additional source premise
is used. Weighted Cauchy--Schwarz, the existing Abel-energy majorant and
the finite Euler harmonic bound prove this classical BRIDGE.

Entry points: `WeilWorkSingularArithmeticCoprimeEnergy.lean:93`,
`exists_forward_coprime_energy`; `WeilWorkSingularArithmeticSieveResidue.lean:47`,
`exists_forward_sieve_residue_tendsto_zero`. Three leaves,328 lines,
nine public theorems. Targeted --old checks, final direct Lean checks and
all nine axiom audits PASS; only standard Lean axioms. Imports wired,
index refreshed; no umbrella/full build. Lint has11 unrelated unreachable
leaves and no owned finding. Stronger r_Q<=C*phi(Q)/Q, V=0, periodic
completeness and WP03 uniform quotient boundedness remain OPEN. No
significant scientific novelty or completed detector is claimed.

## C42: one harmonic condition pays the rough-sign receiver, verified 2026-10-08

For every full-positive source, put d=coneDeviation(lam). Either its
absolute harmonic mass fails the envelope

    for every eta>0, some B>=0 bounds
    sum_(n<=N) |d(n)|/n <= B+eta*log N for every N>=1,

or, for every y>=2, Y>0 and cutoff T, some k>=T satisfies

    sum_(n<=k, all primes p<=y do not divide n) d(n)/n < Y.

This unconditional alternative follows from hW alone. The receiver uses
one harmonic condition in place of the old four NotchSmall fields.
Finite partial summation supplies arbitrarily late small local-mass
scales and the shifted tail bound; Gaussian localization makes all
four error masses small on the same selected scale. The actual source
pays the positive-definite and Dirichlet summability inputs.

Entry point: `WeilWorkSingularArithmeticNotchRoughSign.lean:109`,
`not_harmonic_small_or_rough_sign_of_weilPositiveFull`. Seven leaves,
1079 lines,15 public theorems and one definition. All targeted --old
builds, final direct Lean checks and all15 axiom checks PASS; only
propext, Classical.choice, Quot.sound. Imports wired and index refreshed;
no umbrella/full build. Global lint has12 unrelated unreachable leaves
and no owned finding. Scientific verdict BRIDGE: coefficient isolation,
C41 rigidity and WP03 uniform quotient boundedness remain OPEN.

## C43a: composite harmonic mass is necessary under harmonic smallness, verified 2026-10-08

For every `hW : WeilPositiveFull lam`, with d=coneDeviation(lam), at
least one of these holds: lam equals Lambda on n>=2; d fails the C42
harmonic-small envelope; or sum_(nonprime n) |d(n)|/n diverges.
The alternative has only hW as its source premise. Its receiver proves
equality from harmonic smallness and a summable composite tail, without
a pointwise o(Lambda) condition or a restriction on prime-deviation signs.
No existence of a noncanonical model meeting either condition is claimed.

The proof uses the new harmonic notch receiver, the old exact low/high
arithmetic weights, and ordinary harmonic convergence already forced by
full positivity. The summable composite tail permits increasing the prime
cutoff; the two notch signs then isolate every coefficient. No interchange
of uncontrolled limits is used.

Entry point: `WeilWorkSingularArithmeticCompositeRigidity.lean:73`,
`canonical_or_not_harmonic_small_or_nonprime_mass_diverges`. Two leaves,
233 lines, three public theorems. Targeted --old builds, final direct
`lake env lean` checks and all three axiom audits PASS; only propext,
Classical.choice, Quot.sound. Both imports wired; no full/umbrella build.
Scientific verdict BRIDGE, not significant new science. C43's unrestricted
harmonic-small rigidity, C41, and the WP03 quotient receiver remain OPEN.

## C49: multiplicative strict-local-bound class, paper proof only

A full-positive source whose deviation on n>=2 is multiplicative with
|f(p^k)|<=theta<1 is canonical by the paper argument in PROOF.md.
Its proposed new ingredient is a finite Euler-product real-part bound
forced by the actual notch law. Source analyticity at1 prevents the
vanishing harmonic value of the C47 null-expansion profile. Classical
Caratheodory estimates then force absolute harmonic convergence.

This class theorem is NOT yet Lean-verified. Only the standard analytic
finite-product disk estimate has passed targeted, direct and axiom
checks in WeilWorkSingularArithmeticEulerDisk.lean. No significant
novelty, unrestricted rigidity, or WP03 solution is claimed.

C49 formal progress: WeilWorkSingularArithmeticTorusSign.lean now passes
its final direct audit and all five public axiom audits, using only
standard Lean axioms. It proves the source-to-pointwise-sign implication
when a continuous Fourier density is supplied, with explicit kernel
symmetrization. Constructing C49's Euler density and proving its exact
coefficients remain unpaid. This is another standard bridge, not a
completed class theorem or WP03 detector.

C49 endpoint support: WeilWorkSingularArithmeticHarmonicConvolution.lean
passes targeted --old, final direct and all six axiom audits. It proves
that ordinary harmonic convergence survives convolution by an absolute
harmonic sequence, and that a strict harmonic norm contraction has an
absolute inverse at the same endpoint. The local Euler instantiation
and final class theorem remain in progress.

C49 finite-prime step: WeilWorkSingularArithmeticPrimeDeletion.lean now
proves the exact ordinary harmonic limit after deleting any finite prime
set, divided by its local Euler product. All 15 public theorem axiom
audits and the final direct leaf audit pass; only standard Lean axioms.
The exact arithmetic factorization and same-endpoint local inverses are
proved, not assumed. Gcd-weighted limits, the actual Euler density and
the source rigidity capstone remain unfinished.

C49 gcd coefficients: WeilWorkSingularArithmeticGcdEuler.lean derives
the exact real gcdHarmonicSum limits from multiplicativity, the strict
local coefficient bound and the ordinary harmonic limit. The unit
coefficient contributes -1 explicitly. Final direct audit and all ten
axiom checks pass; only standard axioms. The actual Poisson density,
strict-profile NotchSmall, positive harmonic value and rigidity capstone
remain to be formalized; no C49 or WP03 completion claim.

C49 analytic coefficients: WeilWorkSingularArithmeticPoissonEuler.lean
proves the finite Poisson/Euler density's exact Fourier coefficients for
arbitrary radii in [0,1), with positivity and continuity of each kernel.
Final direct audit and all nine axiom checks pass; standard axioms only.
Its prime-radius/source identification is in progress. The source-forced
Euler-product bound and complete class rigidity are not yet Lean theorems.

C49 source identification: WeilWorkSingularArithmeticSourceEuler.lean
now proves the literal prime-radius Fourier identity, the real gcd
endpoint and the finite Euler real-part inequality. The ordinary
harmonic value comes from the existing full-source theorem. Final
direct audit and all thirteen axiom checks pass; standard axioms only.
Strict-profile NotchSmall remains explicit in this bridge. Its removal,
positive harmonic value and prime-tail rigidity are unfinished. Seven
C49 leaves are wired; C49 and WP03 are not fully formalized or solved.

C49 strict-profile smallness: WeilWorkSingularArithmeticMeanSmall.lean
proves absolute Cesaro mean zero from the uniform strict prime-power
bound, then uniform decay of logarithmic-window mass and NotchSmall.
Its source corollary now supplies ordinary H, H<=1 and all finite Euler
bounds without an added smallness or convergence input. Final direct
and all ten axiom audits pass; standard axioms only. H>0 and the final
prime-tail rigidity upgrade remain unfinished. Eight C49 leaves wired;
no significant novelty or WP03 completion claim.

C49 Euler lower bound: WeilWorkSingularArithmeticPositiveEuler.lean
proves a positive, uniform fractional-zeta lower bound for the actual
multiplicative Dirichlet series on sigma>1. Local logarithm estimates,
absolute Euler-product convergence and the prime-square remainder are
paid. Final direct audit and all nine axiom checks pass; standard axioms
only. The ordinary Abel endpoint and source analytic zero exclusion are
next; H>0 and final class rigidity remain unformalized.

C49 positive normalization: WeilWorkSingularArithmeticHarmonicPositive.lean
identifies the actual analytic source value with ordinary H and proves
H>0 from the strict prime-power profile. Its final corollary supplies
0<H<=1 and all finite Euler real-part bounds with no separate analytic
premise. Final direct13882 and all14 axiom96206 audits pass; standard
axioms only. Ten C49 leaves wired. Prime-tail summability and complete
class rigidity remain unfinished; WP03 remains open.
