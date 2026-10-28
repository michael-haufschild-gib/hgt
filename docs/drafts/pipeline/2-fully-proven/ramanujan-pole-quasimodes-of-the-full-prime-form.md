# Ramanujan pole profiles are quasimodes of the full finite prime form

- **ID:** ramanujan-pole-quasimodes-of-the-full-prime-form
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Source:** RAPT valuation steps and actual finite-sieve adjunction operator; RBG Ramanujan germs; Mertens finite part
- **Count:** uncounted; exact Lean realization and final audits remain

## Target

Let c_m(n) be the Ramanujan sum, m>=1, and let P_N be the literal real symmetric
matrix `weilPrimeKernel(n,k)` for 1<=n,k<=N. Define

`u_(m,N)(n)=c_m(n)/sqrt(phi(m)*n)`,
`E(m)=gamma+log(m)+tameDifferent(m)`.

For every fixed m, the paper proof below establishes

`||P_N u_(m,N)-(log(N)-E(m))u_(m,N)||^2/log(N) -> 0`,
`||u_(m,N)||^2/log(N) -> 1`.

Distinct fixed m have inner product divided by log(N) tending to zero.
Consequently, for each fixed finite conductor packet and every epsilon>0, all
sufficiently large N admit distinct actual matrix eigenvalues simultaneously
within epsilon of `log(N)-E(m)`. This is the exact finite-packet formulation
being formalized. It does not order the entire spectrum or exclude additional eigenvalues.
It supplies no RH or full Weil-test sign inference.

## Connection to audit

For a prime power m=p^k, k>=1, the normalized Ramanujan sum is

`c_(p^k)(n)/sqrt(phi(p^k))`
`=sqrt(phi(p^k))*(1_(v_p(n)>=k)-1/(p-1)*1_(v_p(n)=k-1))`.

The factor in parentheses is the local valuation eigenstep. Coprime conductor
multiplicativity gives the product of those steps used in the proof below.
The stronger literal coefficient identity for every finite-sieve Blaschke
eigenvector is recorded on the coherent-completion backlog card; it is not
an input to the full-matrix residual proof.

For a bounded valuation profile g, divide the actual prime row on g(n)/sqrt(n)
by 1/sqrt(n). The exact up and down divisor sums give

`g(n)*(Mertens(floor(N/n))+log(n))`
`+sum_(p in support(g)) log(p)*sum_(p^j<=N/n) p^(-j)*(g(np^j)-g(n))`
`+sum_(p in support(g)) log(p)*sum_(1<=j<=v_p(n)) (g(n/p^j)-g(n))`.

Replacing each finite up sum by its geometric tail completion gives the actual
local pole-gauge generator. The error is bounded by a constant times the
Mertens remainder, logarithmic floor roundoff, and geometric quotient tails.
All tend to zero when N/n tends to infinity and remain bounded everywhere.
The harmonic boundary-layer lemma makes their squared row error o(log N).
The complete-period Ramanujan Gram supplies the normalized inner products.

Exact row reindexing, the generator/eigenmode identity, uniform error domination,
periodic harmonic transfer, and spectral-distance transfer have the dependency-closed
paper proof below. Their Lean realization remains unverified.

## Novelty leads

- `RAPT/TheValuationTowerIsExactlySolvable.lean` proves pointwise local pole-gauge
  eigenvectors and a sharp finite-class gap. Its formalized card anticipates the
  Kronecker energy list. These are baseline.
- The active finite-sieve adjunction package proves an actual maximal-domain
  operator on supported-integer class coordinates. The proposed target acts on
  every integer up to N with the full literal prime matrix; it requires a new
  row-error estimate, not only convergence of quadratic forms.
- Corpus searches for valuation approximate eigenvectors and Ramanujan prime
  quasimodes found those local equations and generic approximate-eigenvector
  tools, but no instance of this full-matrix assertion.
- `RAPT/TheArchimedeanPlacePaysTheArithmeticPoint.lean` through its joint Gram
  was inspected. Its `jointMode` already uses c_m/sqrt(phi(m)), and
  `periodMean_ramanujanMode_mul` proves exact complete-period orthogonality.
  The normalization and periodic Gram are baseline inputs; the new target is
  their actual full-prime row residual.
- `ALG/TheLocalFactorTricklesDownByRamanujan.lean` was inspected through its
  Ramanujan datum: it concerns the finite-field trace bound, not Ramanujan sums.
- The card `constrained-prolate-arithmetic-dilation-operator-limit.md` was
  inspected through its operator and spectral limit: it concerns a different
  positive dilation-response matrix with an explicit trace-class diagonal limit.

Primary-literature check: Schlage-Puchta's
[Ramanujan determinant paper](https://link.springer.com/article/10.1007/s00013-021-01643-8)
treats a divisor-indexed Ramanujan matrix and integral circulant spectra; its
stated matrices differ from the present Mangoldt divisibility kernel.
Hilberdink's [multiplicative Toeplitz singular-value paper](https://doi.org/10.1080/03081087.2016.1204978)
was checked at the abstract level: it studies triangular arithmetic matrices
and leading singular-value asymptotics. The proposed self-adjoint full-row
residual and conductor-dependent finite offsets are a different assertion.
Hilberdink--Pushnitski's [LCM spectral analysis](https://arxiv.org/html/2401.06892v1)
was inspected through its tensor and counting arguments. It supplies established
methodological context, with a different literal kernel. These checks support
the distinction; they are not a claim of exhaustive worldwide novelty.

The newly formalized `ThePrimeFormHasASpectralGapBelowItsPole.lean` and its
pipeline card were read in full. They prove a uniform positive gap on the pole
complement through harmonic-measure tensorization. They do not identify the
higher conductor offsets or prove actual norm residuals for Ramanujan modes.
The present finite-packet result remains distinct; it does not prove the optimal
gap or exhaust the full spectrum.

A further RAPT-restricted Ramanujan/quasimode search during implementation
returned this package's new completed-row inputs, the existing joint Cesaro
Gram, local tower/sieve constructions, and the new one-gap theorem. Their
claims remain distinct from the full-row residual and finite spectral packet.
The present package is still uncounted until its remaining checks pass.

## Gates

- [x] Complete corpus novelty and significance audit; final recheck remains before counting.
- [x] Dependency-closed paper proof of the actual full-matrix assertion.
- [ ] Exact Lean formalization, direct-source and transitive axiom audits.

Finite-sieve adjunction is formalized. This theorem is undergoing its exact
Lean realization and remains uncounted.

## Additional checked bridges and proof design

The corpus already identifies the primitive-root Ramanujan sum with the real
BVI coefficient: TTPC `ramanujanSum_eq_ramanujanLagCoefficient` and
`ramanujanMode_eq_ramanujanLagCoefficient` in
`ParitySensitiveRamanujanStabilizerTransfer.lean`. BVI
`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean` supplies coprime
multiplicativity and the exact prime-power multiplier. Its
`RamanujanLagCoefficientAndTotientQuotient.lean` gives the gcd-divisor formula.
These discharge the arithmetic identification and unit-multiplication invariance
at the paper level; the eventual Lean bridge should reuse these exact results.
The local step equations and their proof were reread. No local mode formula is new.

RAPT `roundoff_le` in `TheFinitePartIsEulersConstant.lean` gives precisely
`0 <= log N-log(floor(N/n))-log n <= 1/floor(N/n)` for 1<=n<=N.
That module also supplies `mertensSum(y)-log(y) -> -gamma`.
The general real Cesaro-to-logarithmic mean theorem is
`RHTower.pm_tendsto_harmonic_average_of_mean` in
`PMPowerDampedMobiusCovarianceCancellation.lean`. RBG's periodic prefix bound
and the complete-period Gram give its hypotheses for every fixed pair of modes.

No explicit rate for a prime-power tail is needed. For a finite support Q set
`T_p(y)=sum_(a>=1,p^a>y) p^(-a)`. Geometric summability and exhaustion of each
fixed exponent imply `T_p(y)->0`. If |g|<=B, the missing upward correction is
bounded by `2B sum_(p in Q) log(p) T_p(y)`, uniformly in the row n.
Together with Mertens and roundoff this gives a nonnegative function
`F(y)=B*(|mertensSum(y)-log(y)+gamma|+1/y)
      +2B sum_(p in Q)log(p)T_p(y)` tending to zero, with
`|rowResidual(N,n)| <= F(floor(N/n))/sqrt(n)`.
The existing harmonic boundary-layer bound applied to F squared then yields
the required squared residual limit. This avoids imposing a uniform pointwise
row limit near the upper edge of the horizon.

For a finite Hermitian matrix, expanding a nonzero vector x in an orthonormal
eigenbasis gives `min_j |lambda_j-mu| <= ||(A-mu)x||/||x||`: otherwise every
term of the squared residual expansion exceeds the claimed lower bound times
its squared coefficient. This elementary finite-dimensional lemma will be
formalized if no exact corpus instance is found. For a finite set of distinct
arithmetic energies, choose disjoint intervals smaller than one third of their
minimum separation. The residual limits eventually put an actual matrix
eigenvalue in each interval. The target should state the finite-packet result
with an arbitrary prescribed accuracy, and also retain the asymptotically
orthonormal Ramanujan vectors, rather than claim an ordering of the full spectrum.

Additional novelty query restricted to RAPT returned the existing coarse pole
row bound, local tower equations, and the current supported-integer operator;
no full-matrix Ramanujan residual theorem. Whole-corpus and neighbouring
programme exclusions remain part of the final novelty audit.

The formalized `weil-two-pole-matrix-and-integrated-prime-error.md` card was also
read in full. It computes a two-dimensional compression on physical exponential
poles and relates its cross entry to an integrated Chebyshev error. That matrix
and its full-Weil sign problem differ from the full integer prime matrix and
the Ramanujan vector residuals considered here.

The exact quotient limit already exists as
`RHTower.tendsto_harmonicQuotientMean_div_log` in
`RHTower/HarmonicQuotientToeplitz.lean`; its complete source was checked.
A convergent squared majorant is bounded automatically, so it directly supplies
the residual averaging step. No new generic harmonic quotient theorem is needed.

Whole-corpus queries excluding RAPT also returned unrelated objects: the BVI
Ramanujan evaluation/prefix matrix, PM primitive/divisor-energy kernels, and CCM
Guinand-Weil source matrices. The CCM completed-source card was read: it reconstructs
a restricted-Weil matrix on centered cosine modes, not the matrix on positive
integer orders used here. The TTPC parity-twin card was read through its stated
results and proof mechanisms: it computes Abel/digamma germ limits and a local
short-cycle positivity statement, not full prime-matrix quasimodes. AIT search
returned the existing local tower/KMS identities and the literal prime-form
sum over towers. None supplies the present norm-residual limit.

## Paper proof under implementation audit

Fix m>=1 and put g(n)=c_m(n)/sqrt(phi(m)), k_p=v_p(m),
Q={p:p divides m}, and kappa=log(m)+tameDifferent(m). The BVI multiplicativity
and prime-power formula give

`g(n)=product_(p in Q) sqrt(phi(p^k_p))*valuationStep(p,k_p,v_p(n))`.

In particular g is bounded, real, m-periodic, and unchanged by multiplication
or division by a prime power coprime to m. Let B>=0 bound |g|.

For any real profile g, literal divisibility reindexing of the prime row gives

`sum_(j<=N) P(n,j)g(j)/sqrt(j)`
`=1/sqrt(n) * [sum_(t<=N/n) Lambda(t)g(nt)/t
                 +sum_(d divides n) Lambda(d)g(n/d)]`.

The factor n is positive and n<=N. The upward sum includes t=1 harmlessly;
the downward sum includes d=1 harmlessly, because Lambda(1)=0. Subtract g(n)
inside both sums and use `sum_(d divides n)Lambda(d)=log(n)`. This yields

`1/sqrt(n)*[(Mertens(N/n)+log(n))g(n)+C_(N/n)(g,n)]`,

where C_y is the finite upward difference plus the exact downward difference.
`ThePrimeRowsReadPoleProfiles.lean` implements this exact identity for arbitrary g
and passed its scratch and first dependency-olean checks.

The upward difference has an absolutely convergent completion: nonzero terms
have t=p^a with p in Q, and their absolute sum is at most
`2B sum_(p in Q)log(p)/(p-1)`. Define C_infinity by this completion. Changing
only the p-adic valuation leaves every other product factor fixed. Thus its
p-component is log(p) times

`L_p y(v)=sum_(a>=1)p^(-a)(y(v+a)-y(v))
           +sum_(a=1..v)(y(v-a)-y(v))`.

For y=valuationStep(p,k), k>=1, the already proved tower equation says
`L_p y=-(k+1/(p-1))*y`. Directly: below k-1 the one negative upward term cancels
the geometric tail; at k-1 the upward tail and k-1 downward terms give the
same multiplier; at v>=k the downward terms contribute
`-p/(p-1)-(k-1)=-(k+1/(p-1))`, and the upward terms vanish.
Multiplying by the other local factors and summing p gives
`C_infinity(g,n)=-kappa*g(n)`. For m=1 the product and Q are empty,
g=1, kappa=0, and both differences vanish identically.

Let `T_p(y)=sum_(a>=1,p^a>y)p^(-a)` and
`T(y)=2B sum_(p in Q)log(p)T_p(y)`. Absolute convergence gives
`|C_y(g,n)-C_infinity(g,n)|<=T(y)` for every n>=1, independently of n.
Every T_p tends to zero by exhaustion of the summable geometric series;
Q is finite, so T tends to zero. Mertens gives
`e(y)=Mertens(y)-log(y)+gamma -> 0`. The exact roundoff theorem gives
`0<=r(N,n)=log(N)-log(N/n)-log(n)<=1/(N/n)`.
Consequently, with E=gamma+kappa,

`|sum_(j<=N)P(n,j)u(j)-(log(N)-E)u(n)|
 <= [B*(|e(N/n)|+1/(N/n))+T(N/n)]/sqrt(n)`.

The bracket is F(N/n) with F->0. The actual squared residual is nonnegative
and at most `sum_(n<=N)F(N/n)^2/n`. Apply the existing complementary-quotient
harmonic mean theorem to the bounded convergent sequence F squared. Division
by log(N) makes the upper bound tend to zero, proving the target residual limit.

For two fixed conductors m,l, take common period q=m*l. Complete-period
orthogonality gives mean(g_m*g_l)=1 if m=l and 0 otherwise. Subtract that mean;
periodicity bounds every partial sum of the resulting sequence by a fixed
constant. Dividing by N proves its Cesaro mean is zero. The existing
Cesaro-to-logarithmic theorem therefore gives
`sum_(n<=N)g_m(n)g_l(n)/n/log(N) -> [m=l]`.
This proves the norm and cross-inner-product limits of the actual pole profiles.

Finally expand any nonzero vector x in a finite Hermitian eigenbasis. Its
squared residual at mu is
`sum_j (lambda_j-mu)^2*|<e_j,x>|^2`, while its squared norm is
`sum_j |<e_j,x>|^2`. At least one eigenvalue therefore has distance at most
the residual/norm ratio. For each fixed m that ratio tends to zero by the two
limits already proved. Distinct arithmetic energies are separated: choose a
finite prime set containing all prime factors of a fixed finite packet and
apply the proved finite-sieve energy injectivity. With disjoint intervals about
`log(N)-E(m)`, simultaneous eventual residual bounds provide distinct literal
P_N eigenvalues, at every prescribed accuracy. No statement about the other
matrix eigenvalues is used or follows.

All dependencies in this paper argument are identified; the remaining audit is
exact Lean realization of the row correction, arithmetic product identification,
uniform tail estimate, and finite-dimensional spectral transfer. This card stays
at the paper-proof stage and uncounted while those are checked.

## Exact implementation interfaces

Fourteen implementation drafts are written. The Hermitian residual helper passed
scratch and first dependency-olean checks, as did the harmonic quotient square-error
helper and the exact arbitrary-profile row module. The correction-to-residual
module passed scratch and its first required olean check. The valuation-step
identification and coprime correction product rules passed scratch and their
first required olean check, as did the Mangoldt reindexing and completed
prime-power row modules. The all-conductor completed-row module now passes
scratch and its transitive axiom audit (propext, Classical.choice, Quot.sound);
its first required olean passed. The uniform-tail module also passes its
scratch check and transitive endpoint audit; its first required olean passed.
The logarithmic Gram/norm module now also passes scratch, with both transitive
endpoint audits clean; its first required olean passed. Four arithmetic
sources remain unchecked:

- `ThePrimeRowsReadPoleProfiles.lean`: literal arbitrary-profile row identity.
- `HarmonicQuotientSquareError.lean`: the squared-error consequence of the
  existing harmonic quotient theorem.
- `HermitianResidualFindsAnEigenvalue.lean`: actual Hermitian eigenvalue from
  `||Ax-mu*x||^2 < epsilon^2*||x||^2`, using Mathlib's eigenvector basis.
- `TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal.lean`: periodic Cesaro
  transfer, normalized Ramanujan modes, actual logarithmic Gram and norm limits.
- `TheRamanujanModesAreValuationSteps.lean`: prime-power coefficient equals
  totient times valuation step; coprime lag invariance; exact Mangoldt-weighted
  product rules for upward and downward corrections.
- `ThePrimeRowCorrectionControlsTheResidual.lean`: Mertens, floor roundoff,
  and a uniform completed correction imply the actual squared residual limit.
- `PrimePowerMangoldtReindex.lean`: weighted infinite and finite reindexing on
  the positive powers of one prime.
- `TheValuationStepsHaveCompletedPrimeRows.lean`: the exact completed correction
  for prime-power conductors, derived from the existing local tower equation.
- `TheRamanujanPrimeRowsHaveAdjunctionEnergy.lean`: coprime conductor induction
  proves the actual all-integer completed-row identity.
- `TheRamanujanPrimeCorrectionHasAUniformTail.lean`: the summable uniform majorant
  and a vanishing tail bound for the completed correction.
- `TheRamanujanPoleProfilesArePrimeQuasimodes.lean`: normalization and assembly
  of the actual squared residual limit.
- `TheRamanujanAdjunctionEnergiesAreDistinct.lean`: separation of positive
  integer energies by placing each pair inside one finite sieve.
- `TheFullPrimeMatrixHasRamanujanSpectralPoints.lean`: literal Euclidean matrix
  and vectors, actual residual identities, and eventual nearby eigenvalues.
- `TheFullPrimeMatrixRealizesFiniteAdjunctionPackets.lean`: simultaneous distinct
  actual spectral points for each finite conductor packet and prescribed accuracy.

The central arithmetic input is Lean-checked, with a clean transitive axiom audit:

`HasSum (fun t => (c_m(n*t)-c_m(n))*Lambda(t)/t)`
`  (-(log(m)+tameDifferent(m))*c_m(n)
      -sum_(d divides n)(c_m(n/d)-c_m(n))*Lambda(d))`.

An efficient exact proof uses induction on coprime prime-power conductors.
For coprime a,b, a Mangoldt-supported jump t=p^k changes at most one factor:

`(c_a(n*t)-c_a(n))*(c_b(n*t)-c_b(n))*Lambda(t)=0`.

Consequently both corrections obey the product rule with coefficients at n.
This assembles the prime-power tower equations without separately formalizing
a full prime-factor product formula. The existing THIM
`sieveLagMultiplier_mul_lag_of_coprime` supplies lag invariance, and BVI supplies
coprime conductor multiplicativity. Mathlib `Nat.recOnPrimePow` was inspected;
its prime-power step retains the required coprimality.

The complete THIM `CompositeClockWaveletTensorAndPhaseRecovery.lean` source was
also read. Its products, shell support, calibrated phase recovery, and dipole
identities concern lag observations. They supply the coprime invariance used here,
but do not assert a completed Mangoldt row or a full prime-matrix residual limit.

For uniform tails, use the explicit nonnegative majorant

`w_m(t)=2*phi(m)*sum_(p divides m)(if p divides t then Lambda(t)/t else 0)`.

BSU `SieveCoordinateSupNorm.abs_ramanujanLagCoefficient_le_totient` was read.
RAPT `sum_dvd_vonMangoldt_div_le` bounds every finite sum of each local weight;
Mathlib `summable_of_sum_le` therefore proves its summability. The corresponding
tail tends to zero independently of n. The scratch proof uses the nonnegative
series w+f and w-f: each finite sum is bounded by its full sum, and their two
inequalities give the absolute correction error. Thus the proof stays entirely
in real series and discharges its own tail bound.

For one prime, `Function.Injective.hasSum_iff` was located via its generated
`hasProd_iff` source in Mathlib and its exact support condition was inspected.
The map k -> p^(k+1) reindexes the upward correction. The zero-off-range proof
uses RAPT `eq_pow_of_dvd_of_vonMangoldt_ne_zero`. Downward reindexing uses the
same injection on `range(v_p(n))`; the exact finite prime-atom sum proof was read
in `TheFinitePartIsTheTowerForm.lean`. The tower equation then gives the completed
correction by subtracting the geometric constant profile. No numerical experiment
or extra analytic premise is involved.
