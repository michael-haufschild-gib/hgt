/-
# Scalar bookkeeping for named analytic-method scenarios

`Method` stores an arbitrary family label and rational exponent. Its named instances are
calibration records; they contain no exponential sum or proof of an analytic estimate.
The inequalities below compare those records, not every possible method in either family.
Likewise the assigned `True`/`False` flags encode a scenario rather than proving properties
of an arithmetic source. Rational formulas later in the file have the same bookkeeping scope.

Historical declaration names are retained. Their theorem types, not their names, determine
what is proved. In particular this module does not establish an exhaustive method taxonomy,
a family-wide impossibility theorem, or an analytic implication from zero-freeness.
See `docs/drafts/pipeline/1-in-progress/corpus-method-model-semantics-audit.md`.
-/
import GaloisForLFunctions.HTGeometry.CorrelationExponentBridge

namespace HTGeometry

/-- Two labels used by the bookkeeping records; not an exhaustive classification of methods. -/
inductive ToolFamily
  | smooth
  | multiplicative
  deriving DecidableEq, Repr

/-- An assigned family label and rational exponent, with no analytic estimate attached. -/
structure Method where
  family : ToolFamily
  savingExponent : ℚ

/-- Recorded smooth-labelled calibration with saving exponent `1/6`. -/
def vanDerCorputMethod : Method := ⟨ToolFamily.smooth, 1/6⟩

/-- Recorded smooth-labelled calibration with saving exponent `1 - 17/21`. -/
def bourgainMethod : Method := ⟨ToolFamily.smooth, 1 - 17/21⟩

/-- Recorded multiplicative-labelled calibration with saving exponent zero. -/
def halaszMethod : Method := ⟨ToolFamily.multiplicative, 0⟩

/-- A second recorded multiplicative-labelled calibration with saving exponent zero. -/
def amplificationMethod : Method := ⟨ToolFamily.multiplicative, 0⟩

/-- Assigned target saving `1/2` in this exponent model. -/
def lindelofSaving : ℚ := 1/2

@[simp] theorem bourgain_saving : bourgainMethod.savingExponent = 4/21 := by
  unfold bourgainMethod; norm_num

/-- Both named multiplicative calibration records have their assigned zero exponent. -/
theorem multiplicative_family_zero :
    halaszMethod.savingExponent = 0 ∧ amplificationMethod.savingExponent = 0 := by
  constructor <;> rfl

/-- The named Bourgain calibration lies below the assigned target. -/
theorem smooth_family_short : bourgainMethod.savingExponent < lindelofSaving := by
  rw [bourgain_saving]; unfold lindelofSaving; norm_num

/-- Three named calibration records lie below the assigned target; no family-wide quantifier occurs. -/
theorem neither_family_suffices :
    bourgainMethod.savingExponent < lindelofSaving ∧
    halaszMethod.savingExponent < lindelofSaving ∧
    amplificationMethod.savingExponent < lindelofSaving := by
  refine ⟨smooth_family_short, ?_, ?_⟩
  · unfold halaszMethod lindelofSaving; norm_num
  · unfold amplificationMethod lindelofSaving; norm_num

/-- The sum of the two displayed calibration exponents lies below the assigned target. -/
theorem families_do_not_add_up :
    bourgainMethod.savingExponent + halaszMethod.savingExponent < lindelofSaving := by
  rw [bourgain_saving]
  unfold halaszMethod lindelofSaving
  norm_num

/-- Difference between the assigned target and named Bourgain calibration. -/
@[simp] theorem best_shortfall : lindelofSaving - bourgainMethod.savingExponent = 13/42 := by
  rw [bourgain_saving]; unfold lindelofSaving; norm_num

/-- A proposed interface whose joint-use flags and target exponent are supplied as fields. -/
structure JointMethod where
  usesSmooth : Prop
  usesMultiplicative : Prop
  savingExponent : ℚ
  both : usesSmooth ∧ usesMultiplicative
  reaches : savingExponent = lindelofSaving

/-- The exponent is below target when the record is one of the three explicitly listed examples. -/
theorem no_single_family_is_joint (m : Method)
    (h : m = bourgainMethod ∨ m = halaszMethod ∨ m = amplificationMethod) :
    m.savingExponent < lindelofSaving := by
  rcases h with rfl | rfl | rfl
  · exact smooth_family_short
  · unfold halaszMethod lindelofSaving; norm_num
  · unfold amplificationMethod lindelofSaving; norm_num


/-!
### Rational saving model

The displayed saving function and its slope numerator are rational expressions.
Their identities do not instantiate an approximate functional equation.
-/

/-- Self-dual saving of the approximate functional equation at input exponent `θ₀` and block
parameter `x`. -/
def afeSaving (theta x : ℚ) : ℚ := (2 * theta - x) / (1/2 - x)

/-- **At the convexity bound the saving is identically `1`.** -/
theorem afeSaving_convexity {x : ℚ} (hx : x ≠ 1/2) : afeSaving (1/4) x = 1 := by
  unfold afeSaving
  have h : (1:ℚ)/2 - x ≠ 0 := by
    intro hc; apply hx; linarith
  rw [div_eq_one_iff_eq h]
  ring

/-- Numerator of the derivative of the saving in the block parameter. -/
def afeSavingSlopeNumerator (theta : ℚ) : ℚ := 2 * theta - 1/2

/-- **The flat direction occurs exactly at the convexity bound.** -/
theorem afeSaving_flat_iff (theta : ℚ) : afeSavingSlopeNumerator theta = 0 ↔ theta = 1/4 := by
  unfold afeSavingSlopeNumerator
  constructor <;> intro h <;> linarith

/-- **Any subconvexity input breaks the degeneracy, with a strictly negative slope.** -/
theorem afeSaving_slope_neg {theta : ℚ} (h : theta < 1/4) :
    afeSavingSlopeNumerator theta < 0 := by
  unfold afeSavingSlopeNumerator; linarith

/-- At Bourgain's exponent the slope is strictly negative, so the optimum is at the largest admissible
block — the tie is broken toward the critical line. -/
theorem afeSaving_slope_bourgain : afeSavingSlopeNumerator (13/84) < 0 := by
  unfold afeSavingSlopeNumerator; norm_num

/-- The saving at the largest useful block, with Bourgain's input: `4θ₀ = 13/21 < 1`. -/
@[simp] theorem afeSaving_bourgain_at_zero : afeSaving (13/84) 0 = 13/21 := by
  unfold afeSaving; norm_num


/-!
### Recorded conductor thresholds

The following declarations compare assigned conductor exponents.
They contain no character-sum estimate or proof of applicability.
-/

/-- The block-length exponent, relative to the conductor, above which Burgess is nontrivial. -/
def burgessThreshold : ℚ := 1/4

/-- The critical block, as an exponent of the conductor. -/
def criticalBlockExponent : ℚ := 1/2

/-- **Burgess reaches the critical block in the conductor aspect.** -/
theorem burgess_reaches_critical : burgessThreshold < criticalBlockExponent := by
  unfold burgessThreshold criticalBlockExponent; norm_num

/-- The margin by which it does so. -/
@[simp] theorem burgess_margin : criticalBlockExponent - burgessThreshold = 1/4 := by
  unfold criticalBlockExponent burgessThreshold; norm_num

/-- Burgess's subconvex exponent for `L(1/2,χ)` in the conductor aspect. -/
def burgessExponent : ℚ := 3/16

/-- The convexity exponent in the conductor aspect. -/
def conductorConvexity : ℚ := 1/4

/-- **Burgess is subconvex**, by `1/16`. -/
theorem burgess_subconvex : burgessExponent < conductorConvexity := by
  unfold burgessExponent conductorConvexity; norm_num

@[simp] theorem burgess_saving : conductorConvexity - burgessExponent = 1/16 := by
  unfold conductorConvexity burgessExponent; norm_num

/-- Three comparisons among the assigned conductor and smooth calibration constants. -/
theorem aspects_compared :
    burgessThreshold < criticalBlockExponent ∧
    burgessExponent < conductorConvexity ∧
    bourgainMethod.savingExponent < lindelofSaving := by
  exact ⟨burgess_reaches_critical, burgess_subconvex, smooth_family_short⟩


/-!
### Assigned completion rates

The completion rate, threshold rate, and parameter counts are stipulated below.
The comparisons do not prove a modulus lower bound or a character interpolation obstruction.
-/

/-- Assigned linear coefficient for a hypothetical logarithmic modulus cost. -/
def completionLogModulus : ℚ := 1

/-- Logarithm of Burgess's threshold at that modulus, as a multiple of `N`. -/
def burgessLogThreshold : ℚ := completionLogModulus / 4

@[simp] theorem burgessLogThreshold_eq : burgessLogThreshold = 1/4 := by
  unfold burgessLogThreshold completionLogModulus; norm_num

/-- Assigned block growth rate in the completion scenario. -/
def blockLogRate : ℚ := 0

/-- The assigned block rate is smaller than the assigned threshold rate. -/
theorem completion_useless : blockLogRate < burgessLogThreshold := by
  rw [burgessLogThreshold_eq]; unfold blockLogRate; norm_num

/-- Difference between the assigned completion threshold and block rates. -/
@[simp] theorem completion_margin : burgessLogThreshold - blockLogRate = 1/4 := by
  rw [burgessLogThreshold_eq]; unfold blockLogRate; norm_num

/-- Identity function used as a proposed parameter-count model. -/
def characterFreeParameters (omega : ℚ) : ℚ := omega

def primeConditions (piN : ℚ) : ℚ := piN

/-- The supplied rational condition count exceeds the assigned one-parameter count. -/
theorem prime_modulus_overdetermined {piN : ℚ} (h : 1 < piN) :
    characterFreeParameters 1 < primeConditions piN := by
  unfold characterFreeParameters primeConditions; linarith

/-- Two scalar comparisons in the assigned completion scenario; no modulus or character theorem. -/
theorem completion_barrier {piN : ℚ} (h : 1 < piN) :
    characterFreeParameters 1 < primeConditions piN ∧ blockLogRate < burgessLogThreshold :=
  ⟨prime_modulus_overdetermined h, completion_useless⟩


/-!
### Rational block thresholds

These are algebraic identities for the stated threshold formula.
The pinning theorem only excludes two contradictory inequalities on the same rational variable.
-/

/-- Nontriviality threshold for an exponent pair applied at block `t^α`. -/
def blockNontrivialThreshold (kappa lam : ℚ) : ℚ := kappa / (1 - lam + kappa)

/-- **On the line of symmetry the threshold is `2κ`.** -/
theorem blockNontrivialThreshold_selfDual {kappa : ℚ} :
    blockNontrivialThreshold kappa (kappa + 1/2) = 2 * kappa := by
  unfold blockNontrivialThreshold
  have h : (1 : ℚ) - (kappa + 1/2) + kappa = 1/2 := by ring
  rw [h]
  field_simp

/-- At Weyl's pair the threshold is `1/3`. -/
@[simp] theorem threshold_weyl : blockNontrivialThreshold (1/6) (2/3) = 1/3 := by
  unfold blockNontrivialThreshold; norm_num

/-- **At Bourgain's pair the threshold is `13/42 = 2·(13/84)`.** -/
@[simp] theorem threshold_bourgain : blockNontrivialThreshold (13/84) (55/84) = 13/42 := by
  unfold blockNontrivialThreshold; norm_num

/-- The saving formula's numerator is positive exactly below `2θ₀`. -/
theorem saving_positive_iff {theta x : ℚ} : 0 < 2 * theta - x ↔ x < 2 * theta := by
  constructor <;> intro h <;> linarith

/-- **The pinning.**  The saving requires `x < 2θ₀` and nontriviality requires `x > 2θ₀`; the two are
compatible at no value of `x`, and their closures meet only at `x = 2θ₀`. -/
theorem block_parameter_pinned {theta x : ℚ} :
    ¬ (x < 2 * theta ∧ 2 * theta < x) := by
  rintro ⟨h1, h2⟩
  linarith

/-- At the pinned point both degenerate: the saving numerator vanishes and the block bound is exactly
trivial. -/
@[simp] theorem pinned_point_degenerate {theta : ℚ} :
    2 * theta - (2 * theta) = 0 := by ring

/-- At Bourgain's input the pinned block parameter is `13/42`. -/
@[simp] theorem pinned_bourgain : 2 * (13/84 : ℚ) = 13/42 := by norm_num

/-- **Consistency: the pinned point equals the nontriviality threshold at every self-dual pair.** -/
theorem pinned_eq_threshold {kappa : ℚ} :
    2 * kappa = blockNontrivialThreshold kappa (kappa + 1/2) :=
  (blockNontrivialThreshold_selfDual).symm


/-!
### Constant contribution formula

The formula `-alpha/2 + (theta + alpha/2)` equals `theta`.
An analytic estimate connecting this formula to every block is not supplied here.
-/

/-- Contribution exponent of the dyadic block `t^α` to `|ζ(1/2+it)|`, using the self-dual exponent
pair `(θ₀, θ₀+1/2)`. -/
def blockContribution (theta alpha : ℚ) : ℚ := -(alpha/2) + (theta + alpha/2)

/-- **Every block contributes exactly `t^{θ₀}`.** -/
@[simp] theorem blockContribution_const (theta alpha : ℚ) :
    blockContribution theta alpha = theta := by
  unfold blockContribution; ring

/-- The contribution does not depend on the block at all. -/
theorem blockContribution_indep (theta a b : ℚ) :
    blockContribution theta a = blockContribution theta b := by
  rw [blockContribution_const, blockContribution_const]

/-- The rational block-contribution formula returns its input exponent for every block parameter. -/
theorem afe_is_identity_on_exponent (theta : ℚ) :
    (∀ alpha : ℚ, blockContribution theta alpha = theta) := by
  intro alpha; exact blockContribution_const theta alpha

/-- At Bourgain's exponent every block contributes `t^{13/84}`. -/
@[simp] theorem blockContribution_bourgain (alpha : ℚ) :
    blockContribution (13/84) alpha = 13/84 := blockContribution_const _ _

/-- **Nothing to optimise.**  The derivative of the contribution in the block parameter is zero, for
every input exponent — the strongest form of the stationarity results. -/
theorem blockContribution_flat (theta a b : ℚ) :
    blockContribution theta a - blockContribution theta b = 0 := by
  rw [blockContribution_indep theta a b]; ring


/-!
### Assigned applicability flags

Completeness, algebraicity, and coefficient type are assigned Boolean propositions.
Unfolding these flags does not inspect or classify an exponential sum.
-/

/-- Scenario flag assigned `True`; no arithmetic completeness predicate is defined here. -/
def isComplete : Prop := True

/-- Scenario flag assigned `False`; no phase or algebraicity test is defined here. -/
def phaseAlgebraic : Prop := False

/-- Scenario flag assigned `True`; no localized coefficients are constructed here. -/
def localisedRealCoefficients : Prop := True

/-- Conjunction of the two assigned scenario flags. -/
def weilApplicable : Prop := isComplete ∧ phaseAlgebraic

/-- The assigned applicability conjunction is false because its second flag is defined as `False`. -/
theorem weil_inapplicable : ¬ weilApplicable := by
  unfold weilApplicable phaseAlgebraic
  rintro ⟨-, h⟩
  exact h

/-- The assigned coefficient flag holds and the recorded smooth exponent is below target. -/
theorem localisation_gives_vanDerCorput :
    localisedRealCoefficients ∧ bourgainMethod.savingExponent < lindelofSaving :=
  ⟨trivial, smooth_family_short⟩

/-- Assigned truth values together with a scalar exponent comparison; no target sum occurs in the type. -/
theorem target_sum_dichotomy :
    isComplete ∧ ¬ phaseAlgebraic ∧ bourgainMethod.savingExponent < lindelofSaving :=
  ⟨trivial, fun h => h, smooth_family_short⟩


/-!
### Recorded Fourier exponents

The following definitions and comparisons concern rational exponents only.
No Fourier transform or stationary-phase estimate is constructed in these declarations.
-/

/-- Exponent of the trivial bound on the Fourier-side inner product, from `ℓ²`-normalisation. -/
def fourierTrivial : ℚ := 1/2

/-- Exponent required of the inner product for the target. -/
def fourierTarget : ℚ := 0

/-- **The saving required on the Fourier side is `q^{1/2}` — the same as on the original side.** -/
@[simp] theorem fourier_saving : fourierTrivial - fourierTarget = 1/2 := by
  unfold fourierTrivial fourierTarget; norm_num

/-- Exponent of the trivial bound on `T(q)` itself. -/
def targetTrivial : ℚ := 1

/-- Exponent required of `T(q)`. -/
def targetRequired : ℚ := 1/2

/-- The saving required on the original side. -/
@[simp] theorem original_saving : targetTrivial - targetRequired = 1/2 := by
  unfold targetTrivial targetRequired; norm_num

/-- **The reformulation is exponent-neutral: the same `q^{1/2}` must be saved either way.**  What it
changes is the object — an inner product of an `ℓ²`-normalised vector with the quadratic character,
rather than a sum of `q` unimodular terms. -/
theorem reformulation_neutral :
    targetTrivial - targetRequired = fourierTrivial - fourierTarget := by
  rw [original_saving, fourier_saving]

/-- Lower bound for the stationary-phase frequency, as an exponent of `N` at `q = N^{1/3}`:
`h ≥ N/√(2q)` gives exponent `1 - 1/6 = 5/6`. -/
def stationaryFrequencyExponent : ℚ := 5/6

/-- The available frequency range, as an exponent of `N`: `h < q = N^{1/3}`. -/
def frequencyRangeExponent : ℚ := 1/3

/-- The assigned frequency-range exponent is smaller than the assigned stationary exponent. -/
theorem no_stationary_phase : frequencyRangeExponent < stationaryFrequencyExponent := by
  unfold frequencyRangeExponent stationaryFrequencyExponent; norm_num

@[simp] theorem stationary_margin :
    stationaryFrequencyExponent - frequencyRangeExponent = 1/2 := by
  unfold stationaryFrequencyExponent frequencyRangeExponent; norm_num


/-!
### Flat-profile exponent bookkeeping

The exponent `-1/2` is assigned to a hypothetical flat profile.
The resulting identities do not prove that any actual transform is flat.
-/

/-- Exponent of `q` for a flat `ℓ²`-normalised transform. -/
def flatTransformExponent : ℚ := -(1/2)

/-- The assigned flat-profile exponent satisfies the displayed normalization equation. -/
@[simp] theorem parseval_flat : 1 + 2 * flatTransformExponent = 0 := by
  unfold flatTransformExponent; norm_num

/-- Exponent obtained from the flat transform with no cancellation over `h`: `q·q^{-1/2}`. -/
def noCancellationOverH : ℚ := 1 + flatTransformExponent

@[simp] theorem noCancellationOverH_eq : noCancellationOverH = 1/2 := by
  unfold noCancellationOverH flatTransformExponent; norm_num

/-- Exponent with square-root cancellation over `h`: `q^{1/2}·q^{-1/2}`. -/
def sqrtCancellationOverH : ℚ := 1/2 + flatTransformExponent

@[simp] theorem sqrtCancellationOverH_eq : sqrtCancellationOverH = 0 := by
  unfold sqrtCancellationOverH flatTransformExponent; norm_num

/-- **Square-root cancellation over `h` on a flat transform is exactly the target.** -/
theorem sqrt_over_h_is_target : sqrtCancellationOverH = fourierTarget := by
  rw [sqrtCancellationOverH_eq]; rfl

/-- **And without it the bound is exactly the trivial one.** -/
theorem no_cancellation_is_trivial : noCancellationOverH = fourierTrivial := by
  rw [noCancellationOverH_eq]; rfl

/-- The whole saving must come from cancellation in `h` against the quadratic character. -/
@[simp] theorem saving_all_in_h : noCancellationOverH - sqrtCancellationOverH = 1/2 := by
  rw [noCancellationOverH_eq, sqrtCancellationOverH_eq]; norm_num


/-!
### Recorded construction and bound interval

These constants encode a historical comparison. Their rational ordering is proved;
record status, optimality, and analytic attainability are not certified by this module.
-/

/-- Recorded construction exponent used in this calibration model. -/
def bestConstructionExponent : ℚ := 0

/-- Recorded upper-bound exponent used in this calibration model. -/
def bestUpperBoundExponent : ℚ := 17/21

/-- Exponent asserted by the Lindelöf hypothesis. -/
def lindelofExponent : ℚ := 1/2

/-- The assigned target lies strictly between two assigned rational calibration constants. -/
theorem lindelof_strictly_between :
    bestConstructionExponent < lindelofExponent ∧ lindelofExponent < bestUpperBoundExponent := by
  constructor
  · unfold bestConstructionExponent lindelofExponent; norm_num
  · unfold lindelofExponent bestUpperBoundExponent; norm_num

/-- Distance from the construction end to LH. -/
@[simp] theorem gap_below : lindelofExponent - bestConstructionExponent = 1/2 := by
  unfold lindelofExponent bestConstructionExponent; norm_num

/-- Distance from LH to the bound end. -/
@[simp] theorem gap_above : bestUpperBoundExponent - lindelofExponent = 13/42 := by
  unfold bestUpperBoundExponent lindelofExponent; norm_num

/-- Comparison of the two gaps between the three assigned calibration constants. -/
theorem gap_below_larger :
    bestUpperBoundExponent - lindelofExponent < lindelofExponent - bestConstructionExponent := by
  rw [gap_above, gap_below]; norm_num

/-- The total span of the open region. -/
@[simp] theorem total_span : bestUpperBoundExponent - bestConstructionExponent = 17/21 := by
  unfold bestUpperBoundExponent bestConstructionExponent; norm_num


/-!
### Reciprocal-phase exponent bookkeeping

These power-counting formulas do not give a derivative estimate for an actual phase.
A zero first-derivative exponent does not itself exclude other derivative tests.
-/

/-- Exponent of `k` in the reciprocal-phase sum: `k ≍ m q ≍ (N/q)·q = N`. -/
def reciprocalRangeExponent : ℚ := 1

/-- Exponent of the phase `N²/(2k)` at `k ≍ N`. -/
def reciprocalPhaseExponent : ℚ := 2 - reciprocalRangeExponent

@[simp] theorem reciprocalPhaseExponent_eq : reciprocalPhaseExponent = 1 := by
  unfold reciprocalPhaseExponent reciprocalRangeExponent; norm_num

/-- Exponent of the phase derivative `N²/(2k²)` at `k ≍ N`. -/
def reciprocalDerivativeExponent : ℚ := 2 - 2 * reciprocalRangeExponent

/-- **The derivative is of order one — the self-dual regime.** -/
@[simp] theorem reciprocal_derivative_critical : reciprocalDerivativeExponent = 0 := by
  unfold reciprocalDerivativeExponent reciprocalRangeExponent; norm_num

/-- The assigned derivative exponent is zero and not negative; this does not quantify over derivative tests. -/
theorem reciprocal_no_derivative_test :
    reciprocalDerivativeExponent = 0 ∧ ¬ (reciprocalDerivativeExponent < 0) := by
  refine ⟨reciprocal_derivative_critical, ?_⟩
  rw [reciprocal_derivative_critical]
  norm_num

/-- The two recorded reciprocal exponents have their assigned values. -/
theorem reduction_returns_to_correlation :
    reciprocalPhaseExponent = 1 ∧ reciprocalDerivativeExponent = 0 :=
  ⟨reciprocalPhaseExponent_eq, reciprocal_derivative_critical⟩


/-!
### Dual exponent formulas

The following formulas record a proposed change of exponents.
They do not establish Poisson summation or a transformation of arithmetic sums.
-/

/-- Exponent of the dual variable at which the reciprocal phase is stationary: `k_j = √(x/j)`. -/
def reciprocalDualExponent (xExp jExp : ℚ) : ℚ := (xExp - jExp) / 2

/-- The dual phase exponent: `2√(xj)`. -/
def reciprocalDualPhase (xExp jExp : ℚ) : ℚ := (xExp + jExp) / 2

/-- The recorded dual phase exponent unfolds to the arithmetic mean of the input exponents. -/
theorem reciprocal_dual_is_sqrt (xExp jExp : ℚ) :
    reciprocalDualPhase xExp jExp = (xExp + jExp) / 2 := rfl

/-- At the campaign's parameters `x ≍ N²`, `k ≍ N`, the dual variable has `j ≍ x/k² ≍ 1`, and the dual
phase is `2√(x·1) ≍ N` — the same order as the original phase. -/
@[simp] theorem dual_at_campaign_parameters :
    reciprocalDualExponent 2 0 = 1 ∧ reciprocalDualPhase 2 0 = 1 := by
  refine ⟨?_, ?_⟩
  · unfold reciprocalDualExponent; norm_num
  · unfold reciprocalDualPhase; norm_num

/-- Two identities between the recorded dual and original exponent formulas. -/
theorem poisson_neutral :
    reciprocalDualExponent 2 0 = reciprocalRangeExponent ∧
    reciprocalDualPhase 2 0 = reciprocalPhaseExponent := by
  constructor
  · unfold reciprocalDualExponent reciprocalRangeExponent; norm_num
  · rw [reciprocalPhaseExponent_eq]; unfold reciprocalDualPhase; norm_num


/-!
### Deviation-scale bookkeeping

The scale flag is assigned `True`. The inverse-excess formula satisfies the
displayed inequalities; an asymptotic divergence theorem is not encoded by that flag.
-/

/-- Deviation exponent probed by the `2k`-th moment, in powers of `\log\log T`. -/
def momentDeviationScale : ℚ := 1

/-- Deviation exponent relevant to the Lindelöf hypothesis, in powers of `\log T`. -/
def lindelofDeviationScale : ℚ := 1

/-- Scenario flag assigned `True`; it does not state or prove a limit. -/
def scaleSeparationDiverges : Prop := True

/-- Two assigned exponents equal one and the assigned scenario flag is true. -/
theorem deviation_scales_differ :
    momentDeviationScale = 1 ∧ lindelofDeviationScale = 1 ∧ scaleSeparationDiverges :=
  ⟨rfl, rfl, trivial⟩

/-- Moment order required to reach excess `δ`, from Theorem 53. -/
def momentOrderForExcess (delta : ℚ) : ℚ := 1/delta

/-- For `0 < delta <= 1`, the inverse-excess formula is at least one. -/
theorem momentOrder_diverges {delta : ℚ} (hd : 0 < delta) (hd1 : delta ≤ 1) :
    1 ≤ momentOrderForExcess delta := by
  unfold momentOrderForExcess
  rw [le_div_iff₀ hd]
  linarith

/-- Halving a positive rational excess doubles its inverse. -/
theorem momentOrder_doubles {delta : ℚ} (hd : 0 < delta) :
    momentOrderForExcess (delta/2) = 2 * momentOrderForExcess delta := by
  unfold momentOrderForExcess; field_simp


/-!
### Rational zero-free calibration formula

The expression `muFromZeroFree` is a rational function. Its algebra is checked below.
No theorem here assumes analytic zero-freeness and derives an actual zeta bound.
-/

/-- Rational calibration formula, without an attached analytic zero-free implication. -/
def muFromZeroFree (theta : ℚ) : ℚ := (2 * theta - 1) / (4 * theta)

/-- **At `Θ = 1` this is exactly the convexity bound.** -/
@[simp] theorem muFromZeroFree_one : muFromZeroFree 1 = 1/4 := by
  unfold muFromZeroFree; norm_num

/-- The rational calibration formula takes value zero at `1/2`. -/
@[simp] theorem muFromZeroFree_half : muFromZeroFree (1/2) = 0 := by
  unfold muFromZeroFree; norm_num

/-- The threshold for beating Bourgain. -/
def zeroFreeThreshold : ℚ := 21/29

/-- **`Θ = 21/29` gives exactly `13/84`.** -/
@[simp] theorem muFromZeroFree_threshold : muFromZeroFree zeroFreeThreshold = 13/84 := by
  unfold muFromZeroFree zeroFreeThreshold; norm_num

/-- The bound is increasing in `Θ`, so a smaller zero-free abscissa is better. -/
theorem muFromZeroFree_mono {a b : ℚ} (ha : 0 < a) (hab : a < b) :
    muFromZeroFree a < muFromZeroFree b := by
  have hb : (0:ℚ) < b := lt_trans ha hab
  unfold muFromZeroFree
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Beating Bourgain requires `Θ < 21/29`.** -/
theorem beats_bourgain_iff {theta : ℚ} (h : 0 < theta) :
    muFromZeroFree theta < 13/84 ↔ theta < zeroFreeThreshold := by
  unfold muFromZeroFree zeroFreeThreshold
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  constructor <;> intro hh <;> linarith

/-- The rational calibration formula takes value `1/4` at one. -/
theorem known_zerofree_gives_convexity : muFromZeroFree 1 = 1/4 := muFromZeroFree_one

end HTGeometry
