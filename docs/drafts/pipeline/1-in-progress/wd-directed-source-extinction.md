# WD: directed arithmetic source extinction

- **ID:** WD-DIRECTED-SOURCE-EXTINCTION
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, `docs/reports/rh-killed-routes.md`, `docs/reports/review-2810/route-obstacles.md`, `docs/reports/research-programmes.md`
- **Goal:** Close route WD and formalize the arithmetic input unconditionally. A new receiver, obstruction, numerical improvement, or generic kernel identity does not complete this task.

## Exact target

The existing global-cap receiver reduces WD to proving, for one fixed positive parameter in its certified range, that the real part of

\[
 C_\tau(s)=\int_{\mathbb R}
 \operatorname{xiWardSchwarzCapDifference}(\tau,s,x)
 \operatorname{continuedPrimeArchSourceRelativeTrace}
   (\operatorname{xiWardLowerCapPoint}(s,x))\,dx
\]

is nonpositive for almost every canonical transverse level. The corpus already proves the opposite weak inequality and identifies the cap with the strictly-right zero Stieltjes sum. The required new work is the arithmetic upper sign, not this reduction.

Alternative existing endpoints are collision charge below its first nonzero quantum, or all-height finite-head coefficient positivity at arbitrarily small heat. None is proved here.

## Current evidence

- `RHTower/XiWardGlobalCapRightZeroSum.lean`: absolute convergence almost everywhere, exact right-zero sum, nonnegative orientation, vanishing receiver.
- `RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean`: finite-head Prime–Cesàro coefficient formula, polynomial heat inversion, width dictionary. The finite-head sign remains an input.
- `RHTower/XiWardTriangularSourceRectangle.lean`: exact multiplicity-preserving source rectangle responses. Its module statement explicitly leaves the averaged quadratic source budget open.
- `RHTower/XiWardInteriorReflectionAbsorption.lean`: a source-only majorant at probes with real part greater than one half in centered coordinates; critical multiplicity can be retained. This majorant is not an extinction bound.
- `ShallowCauchyPrimeEnergy/ShallowCauchyEnergyBound.lean`: uniformly for small positive shifts, a shallow Cauchy energy bound. At shift `1 / log T` it is `O(T (log T)^2)`.
- `ShallowCauchyPrimeEnergy/ShallowCauchyImplications.lean`: squared-multiplicity, close-pair and simultaneous shallow/deep bounds. Arbitrarily small deep fraction leaves an uncontrolled constant times total count in the shallow channel.

These are source inspections, not fresh compilation claims. Existing unrelated worktree edits, including `HeatFlowNearADeepXiZero.lean`, are preserved.

## Signed-source investigation

The shallow bound uses the pointwise domination in
`ShallowCauchyPrimeEnergy/PoissonKernelDomination.lean`. It replaces the two individual horizontal depths by a common ordinate-only Lorentzian width. Line reflection then gives four identical ordinate contributions. This is appropriate for a size bound, but this stage no longer distinguishes a near-axis reflected pair from its collapsed ordinate mass.

The next object to retain is the signed shift difference of Cauchy responses before that domination. This must be paired with the complete pole–Gamma–prime source. Neither termwise positivity nor a separate absolute bound supplies the required sign:

1. The pointwise-positive annulus idea is already ruled out by
   `cauchy_cross_shift_annulus_neg_of_sq_gt` in `XiWardSourceWindowMultiplicity.lean`.
   Its proved zero-mean identity, `integral_cauchy_cross_shift_annulus_eq_zero`, explains why absolute values lose the cancellation. This is existing evidence, not a new no-go result.
2. Positive Gram energy of the whole annulus would give a lower sign. It does not provide the arithmetic upper budget needed to extinguish strict-right mass.
3. The source rectangle identity retains the necessary signed information, but evaluating and bounding its quadratic products requires the cross-prime, prime–Gamma and endpoint contributions together. **[OPEN CORE]** No upper sign for that complete expression has been established.

The TransThresholdPairCorrelation programme makes the related signed-prime difficulty explicit: its source estimates still require the centered stabilizer discrepancy. Its census conclusions cannot be substituted for WD extinction.

## Further source and heat checks

The quadratic realization is already present, beyond the linear rectangle identity:

- `xiWardPairedSourceRectangleAnnulusEnergy_eq_pair_sum` identifies the source annulus with its full ordered-pair sum.
- `xiWardPairedSourceRectangleAnnulusEnergy_mem_Icc_of_samePacket` in `XiWardPoissonSemigroupDissipation.lean` proves nonnegativity by actual Poisson contraction and bounds the annulus by the narrow source energy.
- `card_mul_three_pi_le_xiWardSlidingSourceRectangleAnnulusEnergy` gives a multiplicity-exact lower charge after sliding localization.

Thus neither building the quadratic realization nor proving its global nonnegativity would advance the open input. The upper bound remains the narrow source energy itself. The exterior source majorant is also insufficient for a difference estimate: from two separate inequalities `A(h) ≤ B(h)` and `A(h+D) ≤ B(h+D)` one cannot infer `A(h)-A(h+D) ≤ B(h)-B(h+D)`. The complementary reflected and critical contributions must be retained and estimated in that difference.

The alternative coefficient investigation uses `XiSliceHeatThresholdTouching.lean`. Its source statements show:

- The global threshold is attained; at a positive threshold some even coefficient vanishes at a finite height and order.
- The zeroth coefficient is strictly positive at positive heat.
- Large heights and large orders are already paid in the threshold argument. The open case is a low positive order on a compact height range whose range depends on the unknown threshold.
- `re_xiSliceHeatTransfer_pos_of_moments_nonneg` transfers an all-height sign for the heated function's slice moments to strict positivity. That sign is a premise; the real-rooted specialization obtains it from real-rootedness of `H_mu`. It cannot be used to exclude contact independently.
- `XiLaguerreMarginUnconditional.lean` proves a falsification implication and the RH-conditional first-Laguerre inequality. Its title does not assert an unconditional all-height sign.

No source-specific estimate excluding positive-order contact has been proved. The next proof attempt must address that actual sign or the complete source energy upper bound; repeating the existing contraction or compactness arguments is not a premise discharge.

## Arithmetic cancellation and theta-source checks

The proposed use of far-prime cancellation must respect the source signs.
`SuzukiCauchyReporterSecantWardCapacity.lean` proves that the raw secant
cross-Gram is nonpositive when one lag is at least twice the other. But the
completed wall is prime minus regular. Its signed cross contribution is
`-(c * Gram(p,q) * d)` for nonnegative weights. Thus that far-region sign
makes the mixed contribution nonnegative, rather than energy-lowering.
`SuzukiCompletedWardCancellativeBand.lean` already proves that a negative
completed mixed contribution requires both lag ratios to be less than two.
This is existing source evidence; it does not establish the needed comparison
inside that band or its transfer to the WD cap.

Two actual theta-source positivity results were also checked:

- `ThetaPrimeGammaCutEnergy.lean` identifies each individual complete
  prime-minus-continuous cut current with
  `integral (t > x) (2 * t * thetaCuspFullSource(t)^2)` and proves strict
  positivity. This is a single-cut statement.
- `ThetaTailTwoPointPositivity.lean` uses the actual negative fourth
  logarithmic derivative to prove the full tail-kernel comparison on two
  real nodes. It does not supply arbitrary mixed-profile positivity.

The precise missing extension is visible in
`CCM/CCMThetaGroundRHCriterion.lean`: complete prime jump energy must dominate
complete Gamma/pole jump energy on every complex smooth ground profile.
The file proves identification and density, while leaving that comparison
unproved. Single-cut positivity cannot be substituted for it.

Likewise, `XiSliceHeatHeightPositiveDefinite.lean` proves nonnegative finite
height Gram forms and a strictly positive central value for every heated
even coefficient. These conclusions concern positive definiteness as a
function of height; they do not assert the pointwise sign at the unknown
positive-order contact height. No missing WD premise was discharged by
these source checks.

## Uniform local heat counts: formalized subtarget

The heat-count programme listed local zero counts uniform as heat tends
to zero as a missing input. The result proved here is a multiplicity-exact `O(log X)`
bound for zeros of `H_t = riemannHeat t` in a fixed window about height `X`,
uniformly for `0 ≤ t ≤ 1/8` and `t log X ≤ 1`. This supplies that input
to local heat dynamics. It does not bound the total nonreal count or
close WD by itself.

Existing ingredients inspected in Lean:

- `XiLineHalfGaussInstance.lean`: the actual Euler-region logarithmic-slope
  error is at most `1/8`, together with strip and far growth comparisons.
- `HalfGaussTransformWindowEstimates.lean`: Gaussian model and slope
  estimates retaining both tails and the strip contribution.
- `KiKimLeeLargeHeightReality.lean`: integrated model error at most `3/10`
  and main-term phase factor at least `23/25` for `t ≤ 1/8`.
- `XiLocalZeroDensity.lean`: multiplicity-exact local counts for the
  unheated function. This does not already prove the heat-uniform target.
- `HeatFlowNearADeepXiZero.lean`: global vertical growth and local
  perturbation bounds. Its `t (log X)^4` scale does not supply the proposed
  `t log X` result.

Proof attempt: use the fixed Euler-side anchor `X - 16i`. Write
`alpha = (1/2) log(X/(2 pi))` and `u = 16 + 2 t alpha`, so `16 ≤ u ≤ 17`.
On `[9/2,32]` compare the Gaussian average with the exact exponential
model, at scale `P = |xiLine X u| exp(-t alpha^2)`. The model error is
already at most `3P/10`. The strip comparison contributes at most
`200(6+X) exp(-(23/2) alpha + 25/16) P`, which tends to zero uniformly
in the indicated heat range. Completing the square removes the large
linear slope from the far tail; its residual Gaussian suppresses that
tail uniformly. Reflection handles the negative half-line. These
estimates should yield a positive fixed fraction of `P` at the anchor.

The tail argument is now explicit. For the model, Chernoff with parameter
one bounds the lower and upper tail ratios by `exp(-10) ≤ 1/32`. For the
actual upper tail put `v = w-u ≥ 15`. Its tilted integrand is bounded by
`P g_t(v) exp(3v + v^2/(2X))`. For `X ≥ 2048` and `t ≤ 1/8`,
`3v + v^2/(2X) + 20 ≤ v^2/(8t)`, so Gaussian absorption bounds its
integral by `2 exp(-20) P ≤ P/32`. The negative Euler half-line has the
additional factor `exp(-16w/t) ≤ exp(-20)` for `w ≥ 9/2`. The two strip
pieces each cost at most `P/32` once `alpha ≥ 8`. Combined with the
`23/25` main-term phase lower bound, this leaves at least `P/4`.
The reverse Euler comparison gives `P ≥ exp(-1/8)|xiLine X 16|`, hence
`|H_t(X-16i)| ≥ |xiLine X 16|/8`.

For the local upper bound, the existing actual-source theorem
`xiSliceReal_le_global` in `XiSliceKKLScaleOffLineDetection.lean` supplies
`|xiLine x w| ≤ |xiLine x 16| exp(B_x |w|+w^2/2)`, where
`B_x = (log x + xiSliceGlobalConstant)/2` and the constant is at most 16.
Gaussian absorption gives
`|H_t(x+iy)| ≤ 4|xiLine x 16| exp(B_x|y|+y^2+2t B_x^2)`.
For `|x-X| ≤ 64`, `|y| ≤ 64`, `log X ≥ 20`, and `t log X ≤ 1`,
the Euler logarithmic derivative comparison and this estimate give
`|H_t(x+iy)| ≤ 4|xiLine X 16| exp(4096+264 log X)`.
Normalize by the latter value and apply Jensen on concentric disks of
radii 18 and 36 about `X-16i`. The inner disk contains every zero with
`|Re z-X| ≤ 1`, because the zero strip is `|Im z| ≤ 1/2`.

The source estimates and multiplicity transport have now compiled
together. The exact theorem is
`RHTower.DeBruijn.exists_sum_zeroMult_riemannHeat_near_le_log` in
`RHTower/HeatLocalZeroDensity.lean`. The source lower and upper estimates
are in `HeatEulerAnchor.lean` and `HeatLocalGrowth.lean`. All three modules
are wired into `RHTower.lean`; final plain-file checks passed without
warnings. The [formalized card](../3-formalized/wd-heat-uniform-local-zero-count.md)
contains the exact ranges, constants, and complete paper proof.

### Inverse-logarithmic persistence: formalized

The complete paper proof, exact Lean declarations, and validation live in
[Mean-field heat persistence](../3-formalized/wd-mean-field-heat-persistence.md).
The cofactor and reverse Gaussian inputs also have a
[formalized record](../3-formalized/wd-heat-local-cofactor-and-reverse-gaussian.md).

The fixed-depth `N₁` persistence scale is proved: an unheated zero of
depth at least `delta>0` near height `X` forces a nonreal zero of `H_t`
in a unit nearby window for `0<t≤c(delta)/log X`, at sufficiently large
`X`. Counting Xi zero copies gives `#F≤C(delta) log X·N(t)` for a deep
dyadic window at the same scale. The earlier `N₂` result had
`log(X)^4` in the denominator. The shrinking-window theorem below now
supplies universal `c delta²` dependence. No upper bound on `N(t)` is proved.

The proof uses the reverse Gaussian identity. If `H_t` has no nonreal
zero in the window, its logarithmic derivative and its derivative are
`O_delta(log X)`, by the actual source bounds, local factorization, and
separation from the remaining real zeros. A holomorphic disk fixed point
solves `s = z + 2t (H_t'/H_t)(s)`. Translating the Gaussian contour to
this saddle cancels the linear logarithmic slope and leaves local error
`O_delta(t log X)`. The global envelope relative to the Euler anchor,
together with the local minimum modulus, controls the complete tail.
The reverse integral differs from 1 by at most `1/2`, contradicting the
unheated zero. All source estimates and this final contradiction are
formalized without an added arithmetic premise.

### Cofactor and window estimates

The cofactor bound is formalized in `HeatLocalCofactor.lean`, without a
heat Hadamard product. The following normalized calculation describes
the bound. Put `c = X-16i` and normalize
`F(w) = H_t(c+w)/H_t(c)`. The anchor and rectangle estimates give
`F(0)=1` and `|F(w)| ≤ B = 32 exp(4096+264 log X)` for `|w| ≤ 40`.
The radius-40 disk stays inside the proved rectangle.

Apply `exists_zero_free_cofactor_bounds` with inner radius 18 and outer
radius 40. It yields a global factorization `F = P g`, where `P` has
degree `n`, all extracted roots have modulus at most 18, `g` is zero-free
on the radius-18 disk, and `|g| ≤ B/22^n` on the radius-40 disk.
At the centre, `|g(0)| ≥ 18^(-n)`, since `F(0)=1` and
`|P(0)| ≤ 18^n`. The already formalized
`sum_multiplicity_mul_log_le` gives
`n log(11/9) ≤ log B`. The maximum-to-anchor ratio for `g` is at most
`B (18/22)^n ≤ B`. Thus `norm_logDeriv_le` in
`HTGeometry/LogDerivativeBound.lean`, with radii 18, 35/2, and 17, gives
`|g'/g| ≤ 140(log B+1)` on the radius-17 disk. Both the degree and
cofactor logarithmic derivative are therefore `O(log X)` uniformly in
the same heat range. Cauchy's derivative estimate on radius 1/4 also
bounds `(g'/g)'` by `560(log B+1)` on the radius-67/4 disk.

The same factorization also provides the missing local normalization for
tail estimates. At `|w|≤17`, `norm_lower_bound_of_ball` gives
`|g(w)| ≥ 18^(-n) exp(-34(log B+1))`. If `w` is at distance at least
`d`, with `0<d≤1`, from every extracted root, then
`|F(w)| ≥ (d/18)^n exp(-34(log B+1))`. Since
`n≤log B/log(11/9)`, this is a lower bound `exp(-C_d log X)`.
The cofactor floor, the degree bound, and the lower bound with the
explicit factor `(d/18)^n` are formalized. `HeatZeroFreeWindow.lean`
converts these data into the `exp(-C_d log X)` floor throughout the
fixed-depth disk.

For `0 < delta ≤ 1/2`, if the unit window has no nonreal heat zero,
a disk of radius `delta/8` about an unheated zero of depth at least
`delta` stays a fixed distance from
every extracted root: real roots are separated vertically and nonreal
roots outside the window horizontally. The polynomial terms then give
`|F'/F| ≤ A_delta log X` and `|(F'/F)'| ≤ B_delta log X` there.
These estimates give the saddle fixed point when `t log X` is
sufficiently small depending on `delta`. The reverse-heat identity,
displaced Gaussian contour, and complete relative tail estimate are
proved and assembled in `HeatMeanFieldPersistence.lean`.

The local saddle error can use the existing
`HTGeometry/LogLinearGronwallModel.lean` directly. If
`a = F'(s)/F(s)` and the derivative of `F'/F` is bounded by `K`, then
on the segment from 0 to a real `u` its slope differs from `a` by at most
`K|u|`. The exponential-model estimate gives
`|F(s+u) exp(-a u)/F(s) - 1| ≤ exp(K u^2)-1`.
Gaussian absorption and the second moment make the integrated local
error at most `8tK`. `HeatGaussianQuadraticError.lean` combines it with
the global envelope to bound the full integral error by
`8tK+8 exp(E-r²/(8t))`; its integrability is proved as well.

`RHTower/HeatLocalCofactor.lean` has passed its plain-file Lean check and
is wired into the umbrella. It contains the actual cofactor
construction and its uniform version. Besides the
degree and two logarithmic-derivative bounds, the uniform theorem retains
the cofactor lower bound and the resulting lower bound for `H_t` at a
point separated from every extracted factor with positive multiplicity.

The full logarithmic derivative can be controlled without differentiating
the polynomial product. Suppose no nonreal heat zero has
`|Re z-X|≤1`, and `z₀` has real part `X` and
`delta≤|Im z₀|≤1/2`, with `0<delta≤1/2`.
Every positive-multiplicity extracted root is at
distance at least `delta` from `z₀`: a real root is separated vertically,
and a nonreal root outside the window horizontally. The cofactor lower
bound gives `|H_t(z₀)|≥|xiLine X 16| exp(-C_delta log X)`.
The disk `B(z₀,delta/2)` is zero-free and lies in the already controlled
rectangle. Applying `norm_logDeriv_le` directly to `H_t` on this disk,
then Cauchy's derivative estimate, gives the two `O_delta(log X)` bounds
needed by the saddle map. These actual-heat disk estimates are proved in
`HeatZeroFreeWindow.lean`; its final plain-file check passed without warnings.

### Reverse heat identity for the saddle

For `t≥0` and `tau>0`, Fubini applied to the actual heated kernel
`Phi(x) exp(t x²)` gives
`H_(t-tau)(z)=integral g_tau(u) H_t(z+u) du`: the Gaussian characteristic
function contributes `exp(-tau x²)`. The heated kernel remains
superexponentially integrable by the existing `mul_exp_sq` theorem.
On each horizontal strip `H_t` is bounded by its positive-kernel
exponential integral. Multiplying by the complex Gaussian gives uniform
real-direction decay, so the existing horizontal-contour theorem permits
every complex translation `b` of the integration line.
With `b=2tau a`, completing the square gives the exact identity

`H_(t-tau)(z) = exp(-tau a²) integral g_tau(u) exp(-a u) H_t(z+2tau a+u) du`.

The identity, arbitrary complex contour translation, and absolute
integrability of the translated integrand are formalized in
`RHTower/HeatReverseGaussian.lean`. Its plain-file Lean check passed
without warnings, and its import is wired.
Taking `tau=t` supplies the reverse identity needed by `(N₁)`. It does
not by itself prove that the integral is nonzero.

## Continuation constraints

- Use the corpus search tool before mathlib; inspect statements before relying on search hits.
- Do not use hgtl7, web search, novelty checks, numerical experiments, or axiom checks; these were explicitly excluded by the user.
- Do not encode the open upper sign as a hypothesis, interface, or imported unproved input.
- Only move a dependency-closed paper proof to `2-fully-proven`; then formalize that exact result directly.
- Compile one file at a time from `formal/` with `lake --old env lean`; no umbrella build or increased proof limits.

## Status

The fixed-depth `(N₁)` persistence and multiplicity counting theorems are
formalized in `HeatMeanFieldPersistence.lean` and
`HeatMeanFieldZeroDensity.lean`. Both, and their four new supporting
modules, passed final plain-file checks without warnings. Earlier local
count, cofactor, and reverse Gaussian inputs are also formalized.
Imports are wired and scratch files removed.

The shrinking-window theorem strengthens this to `c delta²/log X`
with constants and height threshold independent of depth, without an
unproved arithmetic input. It supplies no upper bound on total `N(t)`
and no extinction theorem. The actual source-cap upper sign and
near-axis extinction remain hard blockers.
WD remains open; the thread goal remains active.

### Shrinking zero neighborhoods

The [uniform shrinking-window proof](../3-formalized/wd-shrinking-window-heat-persistence.md)
now gives a heat zero within distance `d` of each
unheated zero whenever `t log X≤c d²`, uniformly over `0<d≤1/2`.
The displacement, nonreal-persistence, and multiplicity-counting
theorems are formalized. All four modules passed final plain Lean checks
without warnings, including the centered-product and actual-window
inputs. Imports are wired and the API scratch file removed.

The necessity transfer now has uniform depth dependence. Further
persistence criteria or constant refinements are not the next target:
the required new input is an arithmetic upper count or source upper sign
strong enough to force extinction.

### Source-sign continuation checkpoint

The subsequent source investigation discharged no new WD premise. No Lean
module was added or recompiled for these checks.

- The quantifiers in
  `ShallowCauchyPrimeEnergy/ShallowCauchyEnergyBound.lean`,
  `exists_uniform_xiShallowCauchyEnergy_le`, are
  `exists C kappa₂, 0<C and 120000<=kappa₂`, followed by uniformity in
  height and shift. Thus `kappa₂` is a fixed smoothing floor, not a
  freely vanishing parameter. Taking `h log T` to zero leaves the
  upper budget `C kappa₂ T log T`. The theorem supplies no vanishing
  collision budget by that limit.
- `CCMThetaThreeEnergyComparison.lean` retains the exact target
  `E_polar <= E_prime + E_Gamma` for every complex smooth ground
  profile. Its unconditional comparison has a small-aperture
  restriction. `ThetaPrimeGammaCutEnergy.lean` proves strict positivity
  for each single cut; `ThetaTailTwoPointPositivity.lean` proves the
  stated two-node comparison. Neither statement proves the mixed
  comparison on the full profile space.
- The heat-height contact and reverse-parabolic proposals were already
  examined in rows 16 and 35 of
  [the sign-producer ledger](wd-la-sign-producer-loop-2026-10-25.md).
  At a contact the displayed terms have compatible nonnegative signs;
  reversing heat gives the wrong comparison direction for propagating
  a lower bound. These are existing failed proposals, not new results.

Do not restart those arguments as missing analytic inputs. The next
source attempt must estimate the complete mixed arithmetic expression
before replacing its depths by an ordinate-only Poisson majorant.
The global inequality, small-time upper count, and extinction remain
open; this checkpoint records no mathematical frontier advancement.

### Heat transport investigation

No new upper-count theorem was obtained from zero transport. The following
source checks delimit the next proof obligation without retiring the
arithmetic upper-count approach.

- `DeBruijnZeroMotion.exists_im_zero_le_of_simple_zero` already gives
  the local velocity `H_t''/H_t'`. Its radius, time interval, and error
  constant depend on the particular simple zero. It is not a uniform
  horizontal-flux estimate through collisions.
- `DeBruijnNonrealCountLocal.lean` already supplies stable multiplicity
  counts on zero-free circles and forward reality near a real zero.
  Rebuilding those local facts would not bound the number of nonreal
  zeros entering a moving height window.
- `HeatFlowSquaredMajorization.sum_roots_polyHeat_sq_sub_le` and
  `DeBruijnNewmanEnergyTransition.riemannHeat_upper_energy_le` control
  squared-height energy. They do not count all surviving shallow roots.
  The existing theorem
  `PolynomialHeatDepthBudgetFailure.twoPairQuartic_depthBudget_fails`
  explicitly separates these statements: for
  `p=(X^2+1)(X^2+9)` and `1/2<=tau<1`, all four heat roots remain
  nonreal although only one initial upper root lies above `sqrt(2 tau)`.
  This polynomial example does not falsify an arithmetic theorem for
  `riemannHeat`; it prevents using a universal depth-count law as its
  missing premise.

A useful transport proof must therefore retain cluster interactions and
derive a uniform arithmetic flux or absorption estimate for the actual
heat function. No such estimate was proved in this investigation. No
Lean source was changed, and existing modules were not recompiled.

### Uniform exterior-force input

The subsequent localized-energy investigation has one new unconditional
analytic input: [the actual exterior-force theorem](../3-formalized/wd-heat-exterior-force.md).
`RHTower.DeBruijn.exists_uniform_riemannHeat_exterior_force` extracts all
actual heat zeros in `|Re z-X|<=2`, with full multiplicity and total
degree `O(log X)`. On the inner rectangle its exterior field satisfies
`|Q|, |Q'| <= C log X` and `|Im Q(z)| <= C log X |Im z|`, uniformly for
`0<=t<=1/8`, `t log X<=1`, including time zero. No spacing or simplicity
assumption is used. The final plain Lean check passed without warnings;
the module is wired into the umbrella.

This pays external vertical drift by squared-height energy. It does not
yet prove the full localized energy inequality or an upper zero count.
[The active flux card](wd-heat-localized-energy-flux.md) records the
pairwise cutoff calculation and the next collision-passage target.
The arithmetic upper sign, near-axis extinction, and WD closure remain
open.

The collision-passage investigation also proves
`exists_ball_simple_riemannHeat_zeros_forward`: every sufficiently small
isolating disk about an arbitrary complex center contains only simple
zeros for all sufficiently close strictly later heat times. The proof
uses the forward Hermite model and exact local multiplicity conservation,
without assuming that the collision center is real. The
[formalized cluster input](../3-formalized/wd-heat-forward-simple-clusters.md)
passed its final plain Lean check without warnings. Weighted zero-sum
continuity and the integrated local energy estimate remain to be proved.

The subsequent continuity theorem,
`continuousOn_heatLocalizedVerticalEnergy`, now proves continuity of the
actual multiplicity-weighted localized vertical energy on all nonnegative
times, including zero. Disjoint isolating disks and preserved total
multiplicity control collisions; the critical strip and compact cutoff
prove the finite-support identities. The
[formalized continuity input](../3-formalized/wd-heat-localized-energy-continuity.md)
passed its final plain check without warnings. Pairwise cutoff dissipation
is also formalized in `HTGeometry/LocalizedHeatPairForce.lean`. The full
actual derivative/integrated inequality and arithmetic upper sign remain
open.
