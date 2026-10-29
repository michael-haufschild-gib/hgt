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

## Continuation constraints

- Use the corpus search tool before mathlib; inspect statements before relying on search hits.
- Do not use hgtl7, web search, novelty checks, numerical experiments, or axiom checks; these were explicitly excluded by the user.
- Do not encode the open upper sign as a hypothesis, interface, or imported unproved input.
- Only move a dependency-closed paper proof to `2-fully-proven`; then formalize that exact result directly.
- Compile one file at a time from `formal/` with `lake --old env lean`; no umbrella build or increased proof limits.

## Status

No new theorem or discharged arithmetic premise yet. No claim of progress across the extinction frontier. WD remains open; the thread goal remains active.
