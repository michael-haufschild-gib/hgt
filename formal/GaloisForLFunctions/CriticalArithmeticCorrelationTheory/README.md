# Critical Arithmetic Correlation Theory

Namespace `GaloisForLFunctions.CriticalArithmeticCorrelationTheory`; umbrella
`CriticalArithmeticCorrelationTheory.lean`.

## Why this programme exists

The explicit formula identifies the arithmetic source of the Riemann zeta function. Existing
programmes identify its negative index, recover its positive collided metric, classify its
arithmetic gauges, and price individual off-line zeros. What remains is an estimate: the signed
prime correlations must be compared with the archimedean and polar contributions at the scale
where a displaced zero is visible.

Critical Arithmetic Correlation Theory studies that comparison. Its subject is the joint use of
addition, multiplication, reflection, and completion to control actual arithmetic correlations.
The central question is how exact arithmetic identities force a quantitative inequality. Source
identification, a positive replacement form, and a conditional receiver do not answer it.

Three principal targets organize the programme:

1. Control the complete low-energy operator through touching and overlapping test atoms.
2. Bound the signed prime-pair functional entering the critical-line census.
3. Bound the annular increment of completed arithmetic source work without assuming finite
   off-line support.

These targets have different logical strengths. A census estimate can tolerate exceptions. A
finite-index estimate can retain finitely many exceptions. Positivity on an exhausting family
must exclude every exception. Constants and quantifiers must reflect the intended conclusion.

## Objects and language

The primary object is the original completed source, with its literal von Mangoldt coefficients,
Gamma contribution, and both pole moments. It is evaluated on finite families of test functions;
the resulting quadratic forms retain mixed terms and the normalization of each test.

An arithmetic correlation carries its additive shift, multiplicative conductor, support, and
scale. A comparison carries the common energy reserve used to pay its error. A limiting statement
carries the invariant it is meant to preserve: sign, negative index, multiplicity, or a counting
proportion. These data cannot be replaced by an unspecified norm or by convergence of selected
matrix entries.

Useful coordinates include:

- **Prime and residue coordinates:** actual integer dilations, successor maps, congruence classes,
  and the centered discrepancy from a parity-compatible Ramanujan model.
- **Spectral coordinates:** conductor modes, pole constraints, and the exact Schur complement left
  after a positive block is eliminated.
- **Microscopic coordinates:** horizontal displacement and ordinate difference in units of
  `1 / log T`, with multiplicities and reflection divided differences retained.
- **Annular coordinates:** differences between two completed source readings at scales `R` and
  `2R`, keeping every exterior field rather than truncating the interaction to the visible zeros.

The language is that of signed quadratic forms, Fourier and Mellin transforms, arithmetic
correspondences, relative spectra, and estimates uniform in explicitly stated parameters.

## Foundational mechanisms

### Signed comparison before absolute estimates

The prime main term cancels a polar contribution. Parity-compatible singular-series terms can
contribute negative repulsion. Estimating their absolute values separately destroys information
that the desired bound needs. A comparison must first identify the exact signed remainder.

### One reserve for interacting directions

If a complete form has block matrix `[[A, B], [B*, D]]` with positive `D`, the unpaid block is
`A - B D⁻¹ B*`. The same reserve cannot also be assigned independently to every mixed term.
Commuting whole-orbit projections provide another exact mechanism: they remove the cross term
before charging the tail. The arithmetic problem is to extend such control to interacting primes
and the original completed form.

### Reflection without a depth gap

An off-line reflected pair can have arbitrarily small displacement. Ordinary value moments can
identify it with two critical points. Divided differences, horizontal jets, and reflected work
retain information that survives this collision. Their arithmetic upper bounds must pay any
normalization cost as displacement tends to zero.

### Annular subtraction

Let `W(R)` denote `ArithmeticElectrostatics.xiDampedSourceWork R`. Its rational height damping is
`h_R(t) = R⁴ / (R² + t²)²`. Subtracting scales before estimating suppresses the constant contribution
of fixed low zeros while preserving a fixed charge at the height of a new quartet. The task is an
upper estimate on the signed source difference, not another proof of its positive zero-side
representation.

### Limits that preserve the intended invariant

Conductor mass can escape while every fixed resolvent reading converges. A finite collection of
generators still has infinitely many translation levels. Convergence must control the full form
domain, its poles, and its tails; it must be uniform in the parameters needed by the receiver.
Explicit escaping profiles may be part of the limit object.

## Pillar theorems supplied by the surrounding corpus

The following are foundations to use, not new claims of this programme.

| Theorem family | Mathematical content | Source programme |
|---|---|---|
| Ordered Weil–Chebyshev identity | Separated mixed entries are exact centered prime-error integrals with completion | ArithmeticIndexDescent |
| Complete bounded spectral counts | Fixed separated profiles have an exhaustive arithmetic description of bounded spectrum | RenormalizedArithmeticPotentialTheory |
| Positivity beyond touching | A fixed smooth profile has eventually positive complete matrices at `c=1+10⁻¹⁸`, and at every fixed smaller positive ratio | TransMetzlerWeilPositivity |
| Whole-orbit dyadic tail | One original Gamma reserve pays every power of the dyadic clock | SignedArithmeticHodgeTheory |
| Parity-compatible stabilizer decomposition | Actual coalescent prime pairs equal their Ramanujan model plus a signed centered discrepancy | TransThresholdPairCorrelation |
| Polynomial-prefix collided metric | Finite arithmetic sources uniformly recover the positive metric on growing normalized families | ConjugateDiagonalGeometry |
| Strict annular quartet quantum | Every off-line quartet forces `W(2|γ|) - W(|γ|) > 39/50` | ArithmeticIndexDescent |
| Finite-support classification | Eventual annular bound by `39/50` is finite support; the bound at every scale is RH | ArithmeticIndexDescent |
| Arithmetic index laws | The complete zeta kernel's index counts distinct right zeros, already on two primes | HeckeKreinToeplitz |

New pillar theorems must add a proved comparison, a quantitative rigidity law, a faithful limiting
tool, or a displacement-sensitive estimate. A restatement of one of these foundations is not a
contribution.

## A source-work comparison theorem

Put `L_R = xiLineTwoLogDerivConstant + log(R+4)`. For every `R ≥ 4`, the actual completed work
satisfies

\[
0\le W(R)\le64R L_R(L_R+1).
\]

Every compactly tapered arithmetic source reading satisfies

\[
|W_N(R)|\le128R L_R(L_R+1)
\]

with the same bound for all taper indices `N`. These are
`xiDampedSourceWork_le_logarithmic_ceiling` and
`abs_xiTaperedSourceWork_le_logarithmic_ceiling` in
[TheCompletedSourceWorkHasALogarithmicCeiling](TheCompletedSourceWorkHasALogarithmicCeiling.lean).

The proof uses the arithmetic Lorentzian mass theorem twice. First, reflection compares each
pair with a unit-width Lorentzian row; its sum is logarithmic in the base height. Second, rational
damping absorbs that height cost into a Lorentzian of width `R`, whose total mass is
`O(log R/R)`. Absolute convergence is established before exchanging the rows. The pole and Gamma
information enters through the completed source identity and the actual log-derivative mass
bound.

This improves the quartic product majorant to `O(R (log R)^2)` and controls the finite arithmetic
readings before the outer cutoff is removed. The estimate is not selective enough to prove finite
exceptions: its positive envelope includes critical zeros. The constant annular target requires
additional signed arithmetic information.

## Complete positivity through touching

Let `φ_η` be the smooth unit-interval plateau from SpacingScaleHarmonicAnalysis,
with transition width `η`. Write `M_η = ∫φ_η²`, `I_η = ∫φ_η`, and
`B_η = bumpRobin(φ_η,1)`. Then

\[
M_\eta\longrightarrow1,\qquad I_\eta\longrightarrow1,\qquad
B_\eta\longrightarrow1,
\qquad
\frac{B_\eta+I_\eta^2}{M_\eta}\longrightarrow2
\quad(\eta\downarrow0).
\]

The lower estimate comes from support overlap: the autocorrelation at shift
`0 ≤ y ≤ 1` is at most `1-y`. Integrating the nonnegative Robin density only
over `[δ,1]` gives

\[
B_\eta\ge(1-\delta)(1-2\eta/\delta).
\]

Together with the existing upper estimate, this proves the exact indicator
limit while keeping every profile smooth. The charge term is essential:
`B_η/M_η + I_η²/M_η - log(2π)` tends to the positive number `2-log(2π)`.

For every `b < 2-log(2π)` and every `ε > 0`, one can choose a single plateau
with `M_η > 1-ε` and a single horizon `N₀` such that, for every `N≥N₀` and
every `0<c≤1`, **every eigenvalue** of its actual normalized complete Weil
matrix is at least `b`. Consequently the entire quadratic form is bounded
below by `b‖x‖²`. Taking `b>0` gives simultaneous positive definiteness through
the touching ratio. Both the profile and the horizon are independent of `c`.

The completed conductor-one energy is
`B_η/M_η-log(2πc)+c I_η²/M_η`. The inequality `-log c ≥ 1-c` bounds it below
by its endpoint value. Strict charge deficit supplies one prime-defect reserve
throughout `(0,1]`; this confines every bounded-energy vector to one finite
Ramanujan family. The actual norm residuals of that family vanish with one
horizon, including the non-ratio boundary prime correction. A hypothetical
low eigenvector would have both a definite coordinate mass in this family
and arbitrarily small coordinates against every member, a contradiction.
The result therefore controls the full matrix. Near-unit mass prevents a
narrow profile from supplying positivity by discarding most nominal support.

The statements are in
[SmoothPlateausRecoverTheCompletedRobinMargin](SmoothPlateausRecoverTheCompletedRobinMargin.lean),
[ThePlateauShapeAndChargeHaveTheirIndicatorLimits](ThePlateauShapeAndChargeHaveTheirIndicatorLimits.lean),
and [OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching](OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching.lean).
The last result strengthens
[SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive](SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean)
by including the endpoint and moving the horizon quantifier before the width
ratio. The horizon can still depend on the chosen profile and on `b`.

Touching refers to the nominal spacing scale. Distinct internal integer log
gaps exceed `1/N`, so these actual supports remain disjoint at `c=1`. At an
index `n` their local coverage fraction is about `n/N`; persistent holes below
the top of the horizon prevent this family from exhausting compact tests.
Neither RH nor positivity on an exhausting overlapping family follows. No
global optimality of `2-log(2π)` over all profiles is asserted.

## Growing conductor families with a square-root horizon

For `Q ≥ 2`, arbitrary real coefficients `a_m`, and every integer horizon `N`,
let

\[
F_a(n)=\sum_{m=1}^{Q}a_m\,
\frac{c_m(n)}{\sqrt{\varphi(m)n}},
\qquad S=\sum_{m=1}^{Q}a_m^2,
\qquad K=Q(Q-1).
\]

Here `c_m(n)` is the actual Ramanujan sum, not a statistical model. The whole
family obeys

\[
(H_N-H_K)S\le\sum_{n=1}^{N}F_a(n)^2,
\]

and, independently of the ordering of `N` and `K`,

\[
\bigl(\log(N+1)-\log(K+1)\bigr)S
\le\sum_{n=1}^{N}F_a(n)^2.
\]

In particular, `log(N+1)-2log Q` is a lower frame constant. The exact logarithmic
constant is positive once `N>Q(Q-1)`. No conductor is held fixed while the
horizon grows, and the bound applies simultaneously to every coefficient vector.

The arithmetic step resolves each normalized Ramanujan sum into primitive roots.
Disjoint exact orders make the root coefficient square mass equal to `S`.
The existing two-sided large-sieve theorem then gives ordinary cumulative mass
at least `(N-K)S`. Nonnegativity improves this to the positive part of that
bound. Summation by parts compares it with constant mass delayed until `K`,
yielding the harmonic loss `H_K`. Monotonicity of `H_n-log(n+1)` supplies the
logarithmic version without an additional constant loss.

[GrowingRamanujanFamiliesHaveASquareRootHorizon](GrowingRamanujanFamiliesHaveASquareRootHorizon.lean)
contains the actual packet and family bounds;
[HarmonicMassFollowsDelayedCounting](HarmonicMassFollowsDelayedCounting.lean)
contains the general transfer. This improves lower frame control beyond the
previous whole-family error proportional to `sum m²`. This whole-prefix
estimate alone does not give matching upper frame control or a small prime
residual at the same growing cutoff. The following annular theorem supplies
two frame bounds on a different family of windows.

For every starting point `A≥0`, length `N≥0`, and the same actual packet,

\[
\left|\sum_{A<n\le A+N}F_a(n)^2
 -(H_{A+N}-H_A)\sum_{m\le Q}a_m^2\right|
\le\frac{Q(Q-1)}{A+1}\sum_{m\le Q}a_m^2.
\]

Shifted large-sieve discrepancy followed by summation against the decreasing
harmonic weights costs exactly their first value `1/(A+1)`. On `(A,2A]`,
the harmonic mass lies between `1/2` and `1`. Thus, when `A≥4Q(Q-1)`,

\[
\frac14\sum_{m\le Q}a_m^2
\le\sum_{A<n\le2A}F_a(n)^2
\le\frac54\sum_{m\le Q}a_m^2.
\]

[AnnularRamanujanFamiliesHaveTwoSidedFrames](AnnularRamanujanFamiliesHaveTwoSidedFrames.lean)
proves both estimates for every real coefficient vector. It also proves an
exact boundary: the literal prime kernel, and hence every prime quadratic
form compressed to one such dyadic annulus, is zero. Distinct integers in
that annulus cannot divide one another. These frames therefore do not give
localized prime quasimodes; the missing prime transport crosses annular
boundaries. No sign estimate for the completed Weil form follows from the
frame bounds alone.

## A uniform cross budget and a strict charge reserve

For a compact profile `g` supported in `[0,w]`, write

\[
G_g(z)=\int g(u)g(u+z)\,du,\qquad
X_g(s)=\int_0^\infty\omega(y)G_g(y-s)\,dy.
\]

The error in replacing the actual cross integral by its center value is
`X_g(s)-ω(s)(∫g)²`. Bounding the density variation at the nearest support point
before integration incurs a factor proportional to `(s-w)⁻²`. The support
boundary supplies the missing payment: a globally `L`-Lipschitz profile satisfies

\[
|G_g(z)|\le\frac{L^2w}{4}(w-|z|)^2,
\qquad
|X_g(s)-\omega(s)(\textstyle\int g)^2|\le19L^2w^3
\quad(0<w<s).
\]

Pairing the endpoint decay with the density increment before integrating
removes dependence on the remaining gap. For each fixed smooth unit profile
`φ` of mass `M>0`, its dilates therefore satisfy

\[
\frac{|X_{\phi_w}(s)-\omega(s)(\int\phi_w)^2|}
 {\int\phi_w^2}\le C_\phi\frac{w^2}{s^2}
\quad(0<w<s),
\]

with one constant for all widths and positive gaps.

A second estimate needs only profile height. If `|g|≤B`, the actual overlap
obeys `|G_g(z)|≤B²(w-|z|)` for `|z|≤w`, and

\[
|X_g(s)-\omega(s)(\textstyle\int g)^2|
\le B^2w(1+w/2).
\]

For dilates of a fixed unit profile and `w≤1`, this yields the explicit
reciprocal-square coefficient `(152(∫|φ|)²+6B²)/M`. For every smooth plateau
with `0<η≤1/4`, one coefficient `316` works independently of `η`. Thus shrinking
transition layers do not force the cross budget to diverge. This refinement is
in [OverlapLengthControlsTheTouchingCrossError](OverlapLengthControlsTheTouchingCrossError.lean).

Distinct integer logarithms
among `1,…,N` have distance strictly greater than `1/N`. Consequently this
estimate controls every entry of the actual cross-error matrix for all
`0<c≤1`, including the endpoint ratio. Reciprocal integer-distance summation
gives the whole quadratic-form budget `4 Cφ c² ‖x‖²` and the square-residual
budget `(36 Cφ A c²)²` on every pole profile `a_n/√n` with `|a_n|≤A`.

The charge has its own strict reserve. Continuity and interval support force
`φ(0)=0`; a nonzero profile cannot agree almost everywhere with a nonzero
constant on `[0,1]`. Its variance gives

\[
q_\phi=\frac{(\int\phi)^2}{M}<1.
\]

Keeping the actual charge `c qφ` in the center estimate yields a single real
floor `aφ` and a single horizon such that, simultaneously for every `0<c≤1`
and all subsequent `N`,

\[
a_\phi\|x\|^2+\frac{1-q_\phi}{4}D_N(x)
\le\mathcal W_{\phi,c,N}(x)
\quad\text{for every }x.
\]

Both constants and the horizon are independent of `c`. The floor need not be
positive. The cross and initial charge results are in
[BoundaryVanishingControlsTheTouchingAutocorrelation](BoundaryVanishingControlsTheTouchingAutocorrelation.lean),
[EndpointDecayRemovesTheCrossKernelGapLoss](EndpointDecayRemovesTheCrossKernelGapLoss.lean),
[TheTouchingCrossMatrixHasAUniformErrorBudget](TheTouchingCrossMatrixHasAUniformErrorBudget.lean),
and [TheChargeDeficitKeepsAUniformPrimeReserve](TheChargeDeficitKeepsAUniformPrimeReserve.lean).
The simultaneous complete reserve is in
[OnePrimeDefectReserveCoversEveryRatioThroughTouching](OnePrimeDefectReserveCoversEveryRatioThroughTouching.lean).

The complete source decomposition retains non-ratio prime lags through products
outside the integer horizon; the next section describes their exact geometry.
Genuine support overlap also changes the atom Gram matrix. Furthermore, the
charge reserve tends to zero when plateaus
approach the unit indicator; uniformity in a fixed profile does not imply
uniform spectral exhaustion in that profile limit.

## The first arithmetic correction is a vanishing boundary star

The endpoint ratio does admit non-ratio prime lags, even though its actual atom
supports remain disjoint. Their geometry is rigid. For `N≥2`, if unequal
positive integers have logarithmic distance at most `1/N` and one belongs to
`1,…,N`, that pair must be `N,N+1`.

Set `d_N=log(N+1)-log N`. For every profile `g` supported in `[0,1/N]`, the
entire non-ratio prime source is therefore exactly

\[
\operatorname{NR}(g,N,x)=2G_g(d_N)x_N
 \sum_{\substack{km=N+1\\ k\ge2,\ 1\le m\le N}}
 \frac{\Lambda(k)}{\sqrt{k}}x_m.
\]

The sum includes all prime powers. This identity retains the boundary term
that the strictly separated formula omits. The divisor identity pays its
weights by `log(N+1)`, giving, for every signed coefficient vector,

\[
|\operatorname{NR}(g,N,x)|\le
2|G_g(d_N)|\log(N+1)\sum_{m\le N}x_m^2.
\]

The remaining support overlap satisfies `1/N-d_N≤1/N²`. If `|φ|≤B` and
`M=∫φ²>0`, the actual endpoint dilation obeys

\[
\frac{|\operatorname{NR}(\phi_{1/N},N,x)|}{\int\phi_{1/N}^2}
\le\frac{2B^2}{M}\frac{\log(N+1)}N\sum_{m\le N}x_m^2.
\]

One bound also covers every `0<c≤1`, with `2B²/M` replaced by `4B²/M` and
`φ_{1/N}` replaced by `φ_{c/N}`. At ratios at most one half the correction is
zero; at the other ratios normalization costs at most a factor two. Every
smooth nonzero compact profile supplies its own finite height bound, so this
is an unconditional source estimate for the programme's actual profiles.

Consequently, for every fixed such profile and every `ε>0`, one horizon makes
the normalized correction at most `ε∑x_m²` simultaneously for all `0<c≤1` and
all coefficient vectors. The exact classification and source identity are in
[OnlyTheBoundaryStarEntersAtTouching](OnlyTheBoundaryStarEntersAtTouching.lean);
the quantitative and uniform eventual bounds are in
[TheBoundaryPrimeStarVanishesAfterNormalization](TheBoundaryPrimeStarVanishesAfterNormalization.lean).

The exact complete decomposition in
[TheCompleteWeilMatrixKeepsItsBoundaryCorrection](TheCompleteWeilMatrixKeepsItsBoundaryCorrection.lean)
combines this correction with the original self term, center, cross error, and
both poles. Its sign is retained. Uniform scalar errors, finite arithmetic
coordinate detection, and the complete norm-quasimode theorem then supply the
positivity result above. Beyond ratio one, additional integer interactions and
the overlapping atom Gram must be handled together; the single-star
classification no longer applies.

## A conductor-uniform arithmetic curvature floor

For a nontrivial conductor `m>1`, define the literal primitive-root energy
and its real arithmetic curvature by

\[
P_m(k)=\sum_{\zeta\text{ primitive of order }m}
 \left|\sum_{j=0}^{k-1}\zeta^j\right|^2,
\qquad
A_m(t)=\sum_{d\mid m}\mu(m/d)d^2
 \{t/d\}(1-\{t/d\}).
\]

Finite root orthogonality and Möbius inversion give the exact identity

\[
P_m(k)=\sum_{d\mid m}\mu(m/d)(k\bmod d)(d-k\bmod d).
\]

The constant mode cancels for `m>1`. On every real cell `k+u`, with
`k≥0` an integer and `0≤u<1`, the same cancellation removes the quadratic
coefficient and gives

\[
A_m(k+u)=(1-u)P_m(k)+uP_m(k+1).
\]

The prefix energy vanishes exactly when `m` divides `k`. Otherwise the
geometric prefix is a nonzero cyclotomic integer. Its nonzero integral norm
has absolute value at least one; its embeddings run through all primitive
roots. Applying the arithmetic–geometric mean to their squared magnitudes
therefore proves `P_m(k)≥φ(m)`. Consecutive integers cannot both be conductor
multiples. Interpolation consequently yields the simultaneous bound

\[
\frac{A_m(t)}{\varphi(m)}\ge\{t\}(1-\{t\})\ge0
\qquad(m>1,\ t\ge0).
\]

The exact identities and vanishing classification are in
[PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder](PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder.lean).
The norm argument and conductor-uniform floor are in
[CyclotomicNormGivesAConductorUniformCurvatureFloor](CyclotomicNormGivesAConductorUniformCurvatureFloor.lean).
These are finite arithmetic theorems. Identifying an integral of this
curvature with a complete overlapping spectral symbol, and realizing that
symbol in the full operator with an exhaustive norm estimate, remain open.

The finite arithmetic excitation also has an exact source description. Put

\[
J_m(n)=\sum_{\substack{d\mid m\\d\mid n}}\mu(m/d)d\log d.
\]

For every positive integer `n`, the literal downward convolution satisfies

\[
\sum_{a\mid n}\Lambda(a)c_m(n/a)=\log n\,c_m(n)-J_m(n).
\]

Thus the existing downward correction equals `-J_m(n)`. At `n=m>0`, every
upward correction vanishes, and the completed prime-row identity gives

\[
\sum_{d\mid m}\mu(m/d)d\log d
=\varphi(m)\bigl(\log m+\operatorname{tameDifferent}(m)\bigr).
\]

[TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet](TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet.lean)
proves these identities directly from the original divisor source. They fix
the logarithmic correction exactly; they do not estimate a growing family
of overlapping norm residuals.

## Questions and tools to develop

**Arithmetic overlap analysis.** What new low modes appear as overlap grows? The surrounding
TransMetzlerWeilPositivity programme already crosses ratio one with an explicit profile and a
prime-defect perturbation estimate. The remaining targets include general profile dependence,
successor corrections at larger ratios, and exhaustion. Derive and estimate the complete
remaining operator, including pole and Gamma terms and the non-diagonal atom Gram. A fixed-ratio
theorem must state whether its horizon is uniform as the ratio changes. The ultimate family
must exhaust the source.

**Mixed prime-action estimates.** Which additive–multiplicative relations allow a joint signed
bound with one energy reserve? Quantify projection and commutator errors. Fixed-prime absolute
costs cannot simply be summed over first prime powers.

**Signed short-difference correlations.** Estimate the actual centered stabilizer discrepancy
with the logarithmic weights and end corrections of its census. The concrete milestones are the
`70%` exchange-rate input and the bandwidth-`4/3` surplus of at most `1/18 + o(1)` for `75%` simple
critical zeros. Model correlations alone do not supply these inequalities.

**Confluent reflection calculus.** Construct observables that distinguish reflected pairs through
coalescence and admit arithmetic upper bounds. Explain their cost at arbitrarily small horizontal
depth. A lower charge with no source estimate leaves the main problem open.

**Quantitative source rigidity.** Convert response information that distinguishes prime gauges
into a completed-form estimate. The error must depend explicitly on conductor and aperture;
fixed precision misses sufficiently remote changes in the prime source.

**Annular arithmetic work.** Establish upper bounds for `W(2R) - W(R)` directly from the completed
arithmetic expression, uniformly as the outer taper is removed. An eventual bound by `39/50`
would imply finite exceptions; the same bound at every `R ≥ 4` would imply RH. The known
classification is an input to research, not an assumption that the bound holds.

**Arithmetic count production.** Find a characteristic-zero mechanism that produces a counting
inequality. Integrality already provides base Chebyshev control; a replacement for the useful
flatness of Frobenius must earn its quadratic estimate. A structure with the desired inequality
as a field would only rename the missing theorem.

## Traps and calibration

The maximal prime gap does not identify zeta: remote prime flips share it. Haar-almost-everywhere
cancellation does not select the actual Möbius gauge. A compact negative perturbation need not
have finite negative index when the positive spectrum approaches zero. Density bounds need not
exclude a single zero. Finite heat counts at each positive time need not be uniformly bounded
near zero. Low-profile positivity does not exclude undiscovered modes unless the spectral count
is exhaustive.

Calibration must match the proposed theorem. Liouville, remote prime flips, small weight changes,
and impure geometric models test different assumptions. A theorem deciding RH must use an
assumption that fails on every applicable countermodel. A statistical theorem need not exclude
every finite exceptional configuration.

## Place among the programmes

ArithmeticCastelnuovoSeveri and ArithmeticOrientationGeometry provide the geometric and index
languages. ArithmeticIndexDescent and SignedArithmeticHodgeTheory expose paid blocks and the
remaining complete source. RenormalizedArithmeticPotentialTheory resolves the separated
arithmetic spectrum. TransMetzlerWeilPositivity supplies an actual first-overlap perturbation
and positivity theorem. TransThresholdPairCorrelation and ShallowCauchyPrimeEnergy provide census
receivers and collision costs. ConjugateDiagonalGeometry supplies source-built positive metrics.
ArithmeticCountingPositivity and ArithmeticCorrelationGeometry explain source selection and its
limits. ArithmeticEffectivityTheory supplies count mechanisms and their current boundary.

This programme connects those tools through quantitative signed comparison. It does not replace
their objects by an abstract positivity axiom. An estimate should carry enough original-source
data to be usable by more than one of these neighbouring languages when a proved transfer exists.

## Success and contribution criteria

A contribution must identify the actual object, prove its estimate or classification without an
unproved analytic premise, preserve the relevant completion and multiplicity, and state all
uniformity and error dependence. It must locate the improvement over existing corpus results.
If a proposed mechanism fails, its sharp boundary or strongest positive survivor must be extracted
and proved.

The programme succeeds through new arithmetic estimates: an overlapping-family sign bound, a
census improvement with its constant, a finite-index bound, or an exclusion estimate that closes
an individual-zero argument. Foundational definitions and exact identities are useful only as
steps toward these tools. The questions above remain research obligations until the corresponding
unconditional theorems have been formalized.
