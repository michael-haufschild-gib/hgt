import GaloisForLFunctions.RHTower.SteinhausEulerPoissonTiltMoments
import GaloisForLFunctions.RHTower.RandomEulerObservableAbscissa

/-!
# Centered prime sums under the exact Euler Poisson product law

The coordinate tilt at `p^(-1/2)` is combined into an actual countable product
probability measure. Its centered prime logarithms are independent. Finite sums
have mean zero and variance between `sum(1/p)/336` and `36*sum(1/p)`.
Their fourth moment is at most `3888*sum(1/p)^2`, and hence at most one fixed
multiple of the squared variance. The variance diverges along growing cutoffs.

The fourth-moment proof uses independence and centering, not symmetry of the
Poisson law. These are source estimates for the BAG tilted-barrier argument;
no barrier survival, critical-mass decay, or recurrence conclusion is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open GaloisForLFunctions.RHTower
namespace RHTower
open SteinhausModel

/-- Critical radius at prime coordinates; zero at all unused coordinates. -/
abbrev steinhausCriticalPrimeRadius (n : ℕ) : ℝ := randomEulerRadius (1 / 2) n

/-- The radius is nonnegative. -/
theorem steinhausCriticalPrimeRadius_nonneg (n : ℕ) : 0 ≤ steinhausCriticalPrimeRadius n :=
  randomEulerRadius_nonneg _ _

/-- Every critical prime radius lies in the proved moment range. -/
theorem steinhausCriticalPrimeRadius_le (n : ℕ) : steinhausCriticalPrimeRadius n ≤ 3 / 4 := by
  have h := randomEulerRadius_le_rho (by norm_num : (0 : ℝ) < 1 / 2) n
  have hs := randomEuler_rpow_neg_sq 2 (1 / 2)
  norm_num [Real.rpow_neg_one] at hs
  have hp := randomEulerRho_pos (1 / 2)
  change steinhausCriticalPrimeRadius n ≤ (2 : ℝ) ^ (-(1 / 2)) at h
  nlinarith

/-- The squared radii are exactly the prime reciprocal weights. -/
theorem steinhausCriticalPrimeRadius_sq (n : ℕ) :
    steinhausCriticalPrimeRadius n ^ 2 = if n.Prime then (n : ℝ)⁻¹ else 0 := by
  by_cases hn : n.Prime
  · simp only [steinhausCriticalPrimeRadius, randomEulerRadius, if_pos hn]
    simpa [Real.rpow_neg_one] using randomEuler_rpow_neg_sq n (1 / 2)
  · simp [steinhausCriticalPrimeRadius, randomEulerRadius, hn]

/-- The exact tilted law of one prime coordinate. -/
def steinhausEulerTiltPrimeMeasure (n : ℕ) : Measure ℝ :=
  steinhausEulerTiltMeasure (steinhausCriticalPrimeRadius n)

instance (n : ℕ) : IsProbabilityMeasure (steinhausEulerTiltPrimeMeasure n) :=
  isProbabilityMeasure_steinhausEulerTiltMeasure (steinhausCriticalPrimeRadius_nonneg n)
    (lt_of_le_of_lt (steinhausCriticalPrimeRadius_le n) (by norm_num))

/-- Consistent countable product of the actual coordinate tilts. -/
def steinhausEulerTiltProductMeasure : Measure Omega :=
  Measure.infinitePi steinhausEulerTiltPrimeMeasure

instance : IsProbabilityMeasure steinhausEulerTiltProductMeasure := by
  unfold steinhausEulerTiltProductMeasure
  infer_instance

/-- Centered real logarithmic increment at one coordinate. -/
def steinhausEulerTiltPrimeTerm (n : ℕ) (x : ℝ) : ℝ :=
  steinhausEulerTiltCenteredLog (steinhausCriticalPrimeRadius n) x

/-- The coordinate increment lifted to the full phase space. -/
def steinhausEulerTiltPrimeVariable (n : ℕ) (ω : Omega) : ℝ :=
  steinhausEulerTiltPrimeTerm n (ω n)

/-- Actual finite sum of centered prime logarithmic increments. -/
def steinhausEulerTiltPrimeSum (P : Finset ℕ) (ω : Omega) : ℝ :=
  ∑ n ∈ P, steinhausEulerTiltPrimeVariable n ω

/-- The coordinate increment is continuous. -/
theorem continuous_steinhausEulerTiltPrimeTerm (n : ℕ) :
    Continuous (steinhausEulerTiltPrimeTerm n) :=
  (continuous_steinhausEulerTiltLog (steinhausCriticalPrimeRadius_nonneg n)
    (lt_of_le_of_lt (steinhausCriticalPrimeRadius_le n) (by norm_num))).add continuous_const

/-- The coordinate increment has its concrete linear envelope. -/
theorem norm_steinhausEulerTiltPrimeTerm_le (n : ℕ) (x : ℝ) :
    ‖steinhausEulerTiltPrimeTerm n x‖ ≤ 6 * steinhausCriticalPrimeRadius n :=
  abs_steinhausEulerTiltCenteredLog_le (steinhausCriticalPrimeRadius_nonneg n)
    (steinhausCriticalPrimeRadius_le n) x

/-- Each lifted increment is measurable. -/
theorem measurable_steinhausEulerTiltPrimeVariable (n : ℕ) :
    Measurable (steinhausEulerTiltPrimeVariable n) :=
  (continuous_steinhausEulerTiltPrimeTerm n).measurable.comp (measurable_pi_apply n)

/-- Every finite prime sum is measurable. -/
theorem measurable_steinhausEulerTiltPrimeSum (P : Finset ℕ) :
    Measurable (steinhausEulerTiltPrimeSum P) := by
  unfold steinhausEulerTiltPrimeSum
  exact Finset.measurable_sum _ fun n _ => measurable_steinhausEulerTiltPrimeVariable n

/-- A finite deterministic envelope for every prime sum. -/
theorem norm_steinhausEulerTiltPrimeSum_le (P : Finset ℕ) (ω : Omega) :
    ‖steinhausEulerTiltPrimeSum P ω‖ ≤ ∑ n ∈ P, 6 * steinhausCriticalPrimeRadius n :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_steinhausEulerTiltPrimeTerm_le n (ω n))

/-- All coordinate powers are integrable under the actual product law. -/
theorem integrable_pow_steinhausEulerTiltPrimeVariable (n k : ℕ) :
    Integrable (fun ω => steinhausEulerTiltPrimeVariable n ω ^ k) steinhausEulerTiltProductMeasure := by
  refine Integrable.of_bound ((measurable_steinhausEulerTiltPrimeVariable n).pow_const k).aestronglyMeasurable
    ((6 * steinhausCriticalPrimeRadius n) ^ k) (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_steinhausEulerTiltPrimeTerm_le n (ω n)) k

/-- All finite-sum powers are integrable under the actual product law. -/
theorem integrable_pow_steinhausEulerTiltPrimeSum (P : Finset ℕ) (k : ℕ) :
    Integrable (fun ω => steinhausEulerTiltPrimeSum P ω ^ k) steinhausEulerTiltProductMeasure := by
  refine Integrable.of_bound ((measurable_steinhausEulerTiltPrimeSum P).pow_const k).aestronglyMeasurable
    ((∑ n ∈ P, 6 * steinhausCriticalPrimeRadius n) ^ k) (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_steinhausEulerTiltPrimeSum_le P ω) k

/-- The centered prime increments are independent. -/
theorem iIndepFun_steinhausEulerTiltPrimeVariable :
    iIndepFun steinhausEulerTiltPrimeVariable steinhausEulerTiltProductMeasure :=
  iIndepFun_infinitePi fun n => (continuous_steinhausEulerTiltPrimeTerm n).measurable

private theorem integral_variable_pow (n k : ℕ) :
    ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ k ∂steinhausEulerTiltProductMeasure =
      ∫ x, steinhausEulerTiltPrimeTerm n x ^ k ∂steinhausEulerTiltPrimeMeasure n := by
  have hm := Measure.infinitePi_map_eval steinhausEulerTiltPrimeMeasure n
  have hh := integral_map (μ := steinhausEulerTiltProductMeasure)
    (measurable_pi_apply n).aemeasurable
    (((continuous_steinhausEulerTiltPrimeTerm n).measurable.pow_const k).aestronglyMeasurable)
  change (∫ x, steinhausEulerTiltPrimeTerm n x ^ k
    ∂(Measure.map (fun ω : Omega => ω n) (Measure.infinitePi steinhausEulerTiltPrimeMeasure))) = _ at hh
  rw [hm] at hh
  exact hh.symm

/-- Every actual prime increment is centered. -/
theorem integral_steinhausEulerTiltPrimeVariable (n : ℕ) :
    ∫ ω, steinhausEulerTiltPrimeVariable n ω ∂steinhausEulerTiltProductMeasure = 0 := by
  have hh := integral_variable_pow n 1
  simp only [pow_one] at hh
  rw [hh]
  exact integral_steinhausEulerTiltCenteredLog (steinhausCriticalPrimeRadius_nonneg n)
    (lt_of_le_of_lt (steinhausCriticalPrimeRadius_le n) (by norm_num))

/-- Every finite prime sum is centered. -/
theorem integral_steinhausEulerTiltPrimeSum (P : Finset ℕ) :
    ∫ ω, steinhausEulerTiltPrimeSum P ω ∂steinhausEulerTiltProductMeasure = 0 := by
  unfold steinhausEulerTiltPrimeSum
  rw [integral_finsetSum _ fun n _ => by simpa using integrable_pow_steinhausEulerTiltPrimeVariable n 1]
  exact Finset.sum_eq_zero fun n _ => integral_steinhausEulerTiltPrimeVariable n

private theorem integral_variable_sq_bounds (n : ℕ) :
    steinhausCriticalPrimeRadius n ^ 2 / 336 ≤
      ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 2 ∂steinhausEulerTiltProductMeasure ∧
    (∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 2 ∂steinhausEulerTiltProductMeasure) ≤
      36 * steinhausCriticalPrimeRadius n ^ 2 := by
  rw [integral_variable_pow]
  constructor
  · exact integral_sq_steinhausEulerTiltCenteredLog_lower (steinhausCriticalPrimeRadius_nonneg n)
      (steinhausCriticalPrimeRadius_le n)
  · have hh := integral_pow_steinhausEulerTiltCenteredLog_upper (steinhausCriticalPrimeRadius_nonneg n)
      (steinhausCriticalPrimeRadius_le n) 2
    simpa only [steinhausEulerTiltPrimeTerm, steinhausEulerTiltPrimeMeasure, sq_abs,
      mul_pow, show (6 : ℝ) ^ 2 = 36 by norm_num] using hh

private theorem integral_variable_four_le (n : ℕ) :
    ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 4 ∂steinhausEulerTiltProductMeasure ≤
      1296 * steinhausCriticalPrimeRadius n ^ 4 := by
  rw [integral_variable_pow]
  have hh := integral_pow_steinhausEulerTiltCenteredLog_upper (steinhausCriticalPrimeRadius_nonneg n)
    (steinhausCriticalPrimeRadius_le n) 4
  have ha (x : ℝ) : |x| ^ 4 = x ^ 4 := by rw [show 4 = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  simpa only [steinhausEulerTiltPrimeTerm, steinhausEulerTiltPrimeMeasure, ha,
    mul_pow, show (6 : ℝ) ^ 4 = 1296 by norm_num] using hh

private theorem sum_indep_variable (P : Finset ℕ) {n : ℕ} (hn : n ∉ P) :
    IndepFun (steinhausEulerTiltPrimeSum P) (steinhausEulerTiltPrimeVariable n)
      steinhausEulerTiltProductMeasure := by
  have h := iIndepFun_steinhausEulerTiltPrimeVariable.indepFun_finsetSum_of_notMem
    measurable_steinhausEulerTiltPrimeVariable hn
  convert h using 1
  ext ω
  simp [steinhausEulerTiltPrimeSum]

private theorem integral_sum_pow_mul_variable_pow (P : Finset ℕ) {n : ℕ} (hn : n ∉ P) (a b : ℕ) :
    ∫ ω, steinhausEulerTiltPrimeSum P ω ^ a * steinhausEulerTiltPrimeVariable n ω ^ b
        ∂steinhausEulerTiltProductMeasure =
      (∫ ω, steinhausEulerTiltPrimeSum P ω ^ a ∂steinhausEulerTiltProductMeasure) *
        ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ b ∂steinhausEulerTiltProductMeasure :=
  ((sum_indep_variable P hn).comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_fun_mul_eq_mul_integral
    ((measurable_steinhausEulerTiltPrimeSum P).pow_const a).aestronglyMeasurable
    ((measurable_steinhausEulerTiltPrimeVariable n).pow_const b).aestronglyMeasurable

private theorem integrable_sum_pow_mul_variable_pow (P : Finset ℕ) {n : ℕ} (hn : n ∉ P) (a b : ℕ) :
    Integrable (fun ω => steinhausEulerTiltPrimeSum P ω ^ a * steinhausEulerTiltPrimeVariable n ω ^ b)
      steinhausEulerTiltProductMeasure :=
  ((sum_indep_variable P hn).comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integrable_mul
    (integrable_pow_steinhausEulerTiltPrimeSum P a) (integrable_pow_steinhausEulerTiltPrimeVariable n b)

private theorem sum_insert (P : Finset ℕ) {n : ℕ} (hn : n ∉ P) (ω : Omega) :
    steinhausEulerTiltPrimeSum (insert n P) ω =
      steinhausEulerTiltPrimeSum P ω + steinhausEulerTiltPrimeVariable n ω := by
  simp [steinhausEulerTiltPrimeSum, Finset.sum_insert hn, add_comm]

private theorem secondMoment_insert (P : Finset ℕ) {n : ℕ} (hn : n ∉ P) :
    ∫ ω, steinhausEulerTiltPrimeSum (insert n P) ω ^ 2 ∂steinhausEulerTiltProductMeasure =
      (∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure) +
        ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 2 ∂steinhausEulerTiltProductMeasure := by
  have hprod : Integrable (fun ω => steinhausEulerTiltPrimeSum P ω * steinhausEulerTiltPrimeVariable n ω)
      steinhausEulerTiltProductMeasure := by
    simpa only [pow_one] using integrable_sum_pow_mul_variable_pow P hn 1 1
  have heq : ∀ ω, steinhausEulerTiltPrimeSum (insert n P) ω ^ 2 =
      steinhausEulerTiltPrimeSum P ω ^ 2 +
      2 * (steinhausEulerTiltPrimeSum P ω * steinhausEulerTiltPrimeVariable n ω) +
      steinhausEulerTiltPrimeVariable n ω ^ 2 := by intro ω; rw [sum_insert P hn]; ring
  simp_rw [heq]
  have hA := integral_add (integrable_pow_steinhausEulerTiltPrimeSum P 2) (hprod.const_mul 2)
  have hB := integral_add ((integrable_pow_steinhausEulerTiltPrimeSum P 2).add (hprod.const_mul 2))
    (integrable_pow_steinhausEulerTiltPrimeVariable n 2)
  simp only [Pi.add_apply] at hA hB
  rw [hB, hA, integral_const_mul]
  have hz := integral_sum_pow_mul_variable_pow P hn 1 1
  simp only [pow_one, integral_steinhausEulerTiltPrimeSum, integral_steinhausEulerTiltPrimeVariable,
    zero_mul] at hz
  rw [hz]
  ring

/-- Exact variance additivity for the actual independent prime sums. -/
theorem integral_sq_steinhausEulerTiltPrimeSum (P : Finset ℕ) :
    ∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure =
      ∑ n ∈ P, ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 2 ∂steinhausEulerTiltProductMeasure := by
  induction P using Finset.induction_on with
  | empty => simp [steinhausEulerTiltPrimeSum]
  | @insert n P hn ih => rw [secondMoment_insert P hn, ih, Finset.sum_insert hn]; ring

/-- Two-sided variance bounds in terms of the literal prime reciprocal mass. -/
theorem integral_sq_steinhausEulerTiltPrimeSum_bounds (P : Finset ℕ) :
    (∑ n ∈ P, steinhausCriticalPrimeRadius n ^ 2) / 336 ≤
      ∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure ∧
    (∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure) ≤
      36 * ∑ n ∈ P, steinhausCriticalPrimeRadius n ^ 2 := by
  rw [integral_sq_steinhausEulerTiltPrimeSum, Finset.sum_div, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun n _ => (integral_variable_sq_bounds n).1,
    Finset.sum_le_sum fun n _ => (integral_variable_sq_bounds n).2⟩

private theorem fourthMoment_insert (P : Finset ℕ) {n : ℕ} (hn : n ∉ P) :
    ∫ ω, steinhausEulerTiltPrimeSum (insert n P) ω ^ 4 ∂steinhausEulerTiltProductMeasure =
      (∫ ω, steinhausEulerTiltPrimeSum P ω ^ 4 ∂steinhausEulerTiltProductMeasure) +
      6 * (∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure) *
        (∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 2 ∂steinhausEulerTiltProductMeasure) +
      ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 4 ∂steinhausEulerTiltProductMeasure := by
  have heq : ∀ ω, steinhausEulerTiltPrimeSum (insert n P) ω ^ 4 =
      steinhausEulerTiltPrimeSum P ω ^ 4 +
      4 * (steinhausEulerTiltPrimeSum P ω ^ 3 * steinhausEulerTiltPrimeVariable n ω ^ 1) +
      6 * (steinhausEulerTiltPrimeSum P ω ^ 2 * steinhausEulerTiltPrimeVariable n ω ^ 2) +
      4 * (steinhausEulerTiltPrimeSum P ω ^ 1 * steinhausEulerTiltPrimeVariable n ω ^ 3) +
      steinhausEulerTiltPrimeVariable n ω ^ 4 := by intro ω; rw [sum_insert P hn]; ring
  have h₄ := integrable_pow_steinhausEulerTiltPrimeSum P 4
  have h₃₁ := (integrable_sum_pow_mul_variable_pow P hn 3 1).const_mul 4
  have h₂₂ := (integrable_sum_pow_mul_variable_pow P hn 2 2).const_mul 6
  have h₁₃ := (integrable_sum_pow_mul_variable_pow P hn 1 3).const_mul 4
  have hn₄ := integrable_pow_steinhausEulerTiltPrimeVariable n 4
  simp_rw [heq]
  have hA := integral_add h₄ h₃₁
  have hB := integral_add (h₄.add h₃₁) h₂₂
  have hC := integral_add ((h₄.add h₃₁).add h₂₂) h₁₃
  have hD := integral_add (((h₄.add h₃₁).add h₂₂).add h₁₃) hn₄
  simp only [Pi.add_apply] at hA hB hC hD
  rw [hD, hC, hB, hA]
  simp_rw [integral_const_mul, integral_sum_pow_mul_variable_pow P hn]
  simp only [pow_one, integral_steinhausEulerTiltPrimeSum, integral_steinhausEulerTiltPrimeVariable,
    mul_zero, zero_mul, add_zero]
  ring

/-- The fourth moment is controlled by squared prime reciprocal mass. -/
theorem integral_four_steinhausEulerTiltPrimeSum_le (P : Finset ℕ) :
    ∫ ω, steinhausEulerTiltPrimeSum P ω ^ 4 ∂steinhausEulerTiltProductMeasure ≤
      3888 * (∑ n ∈ P, steinhausCriticalPrimeRadius n ^ 2) ^ 2 := by
  induction P using Finset.induction_on with
  | empty => simp [steinhausEulerTiltPrimeSum]
  | @insert n P hn ih =>
    rw [fourthMoment_insert P hn, Finset.sum_insert hn]
    have hS := (integral_sq_steinhausEulerTiltPrimeSum_bounds P).2
    have hn₂ := (integral_variable_sq_bounds n).2
    have hn₄ := integral_variable_four_le n
    have hS0 : 0 ≤ ∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure :=
      integral_nonneg fun _ => sq_nonneg _
    have hn0 : 0 ≤ ∫ ω, steinhausEulerTiltPrimeVariable n ω ^ 2 ∂steinhausEulerTiltProductMeasure :=
      integral_nonneg fun _ => sq_nonneg _
    have hsum0 : 0 ≤ ∑ k ∈ P, steinhausCriticalPrimeRadius k ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hp := mul_le_mul hS hn₂ hn0 (by positivity : 0 ≤ 36 * ∑ k ∈ P, steinhausCriticalPrimeRadius k ^ 2)
    nlinarith [sq_nonneg (steinhausCriticalPrimeRadius n ^ 2)]

/-- Uniform fourth-to-second-moment ratio, with no distributional symmetry premise. -/
theorem integral_four_steinhausEulerTiltPrimeSum_le_sq_second (P : Finset ℕ) :
    ∫ ω, steinhausEulerTiltPrimeSum P ω ^ 4 ∂steinhausEulerTiltProductMeasure ≤
      (3888 * 336 ^ 2 : ℝ) *
        (∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure) ^ 2 := by
  have h := (integral_sq_steinhausEulerTiltPrimeSum_bounds P).1
  have hsum0 : 0 ≤ ∑ n ∈ P, steinhausCriticalPrimeRadius n ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv0 : 0 ≤ ∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure :=
    integral_nonneg fun _ => sq_nonneg _
  have hs : (∑ n ∈ P, steinhausCriticalPrimeRadius n ^ 2) ≤
      336 * (∫ ω, steinhausEulerTiltPrimeSum P ω ^ 2 ∂steinhausEulerTiltProductMeasure) := by linarith
  have hs2 := pow_le_pow_left₀ hsum0 hs 2
  have h4 := integral_four_steinhausEulerTiltPrimeSum_le P
  nlinarith

/-- The actual tilted prime-sum variance diverges at the critical exponent. -/
theorem tendsto_integral_sq_steinhausEulerTiltPrimeSum_atTop :
    Filter.Tendsto (fun N => ∫ ω, steinhausEulerTiltPrimeSum (Finset.range N) ω ^ 2
      ∂steinhausEulerTiltProductMeasure) Filter.atTop Filter.atTop := by
  have hnn (n : ℕ) : 0 ≤ steinhausCriticalPrimeRadius n ^ 2 / 336 := by positivity
  have hnot : ¬ Summable (fun n => steinhausCriticalPrimeRadius n ^ 2 / 336) := by
    intro hsum
    have hh := hsum.mul_left (336 : ℝ)
    apply not_summable_ite_prime_rpow (t := 1) (by norm_num)
    refine hh.congr fun n => ?_
    rw [steinhausCriticalPrimeRadius_sq]
    split
    · simp [Real.rpow_neg_one]
      ring
    · simp
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).1 hnot
  apply Filter.tendsto_atTop_mono (fun N => ?_) hdiv
  simpa only [Finset.sum_div] using (integral_sq_steinhausEulerTiltPrimeSum_bounds (Finset.range N)).1

end RHTower
