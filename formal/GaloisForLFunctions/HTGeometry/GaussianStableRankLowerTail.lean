import Mathlib.Probability.Moments.SubGaussian
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem measure_weightedBernoulli_sum_le_of_iIndepFun
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : I → Ω → ℝ} (hindep : iIndepFun B μ)
    (hmeas : ∀ i, AEMeasurable (B i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, B i ω ∈ Icc (0 : ℝ) 1)
    {p θ : ℝ} (hmean : ∀ i, ∫ ω, B i ω ∂μ = p)
    (hθ : θ ≤ p) (weight : I → ℝ≥0) :
    μ.real {ω |
        ∑ i, (weight i : ℝ) * B i ω ≤
          θ * ∑ i, (weight i : ℝ)} ≤
      Real.exp
        (-2 * (p - θ) ^ 2 * (∑ i, (weight i : ℝ)) ^ 2 /
          ∑ i, (weight i : ℝ) ^ 2) := by
  let X : I → Ω → ℝ := fun i ω => (weight i : ℝ) * (p - B i ω)
  have hXindep : iIndepFun X μ :=
    hindep.comp (fun i x => (weight i : ℝ) * (p - x))
      (fun _ => by fun_prop)
  have hXsub : ∀ i, HasSubgaussianMGF (X i) ((weight i / 2) ^ 2) μ := by
    intro i
    have hproxy :
        ((‖(weight i : ℝ) * p - (weight i : ℝ) * (p - 1)‖₊ / 2) ^ 2 : ℝ≥0) =
          (weight i / 2) ^ 2 := by
      apply NNReal.eq
      simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
        coe_nnnorm]
      rw [show (weight i : ℝ) * p - (weight i : ℝ) * (p - 1) =
        (weight i : ℝ) by ring]
      rw [Real.norm_eq_abs, abs_of_nonneg (weight i).coe_nonneg]
    rw [← hproxy]
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    · exact (hmeas i).const_sub p |>.const_mul (weight i : ℝ)
    · filter_upwards [hbound i] with ω hω
      dsimp [X]
      constructor
      · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hω.2 p)
          (weight i).coe_nonneg
      · exact mul_le_mul_of_nonneg_left
          (by simpa using sub_le_sub_left hω.1 p) (weight i).coe_nonneg
    · dsimp [X]
      rw [integral_const_mul,
        integral_sub (integrable_const p)
          (Integrable.of_mem_Icc 0 1 (hmeas i) (hbound i)),
        hmean i]
      simp
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hXindep (s := Finset.univ) (fun i _ => hXsub i)
    (show 0 ≤ (p - θ) * ∑ i, (weight i : ℝ) by positivity)
  have hevent :
      {ω | ∑ i, (weight i : ℝ) * B i ω ≤
          θ * ∑ i, (weight i : ℝ)} =
        {ω | (p - θ) * ∑ i, (weight i : ℝ) ≤ ∑ i, X i ω} := by
    ext ω
    simp only [mem_setOf_eq, X]
    have hsum : (∑ i, (weight i : ℝ) * (p - B i ω)) =
        p * ∑ i, (weight i : ℝ) - ∑ i, (weight i : ℝ) * B i ω := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    constructor
    · intro h
      calc
        (p - θ) * ∑ i, (weight i : ℝ) =
            p * ∑ i, (weight i : ℝ) -
              θ * ∑ i, (weight i : ℝ) := by ring
        _ ≤ p * ∑ i, (weight i : ℝ) -
              ∑ i, (weight i : ℝ) * B i ω := sub_le_sub_left h _
    · intro h
      have h' : p * ∑ i, (weight i : ℝ) -
          (p - θ) * ∑ i, (weight i : ℝ) ≥
            ∑ i, (weight i : ℝ) * B i ω := by linarith
      calc
        ∑ i, (weight i : ℝ) * B i ω ≤
            p * ∑ i, (weight i : ℝ) -
              (p - θ) * ∑ i, (weight i : ℝ) := h'
        _ = θ * ∑ i, (weight i : ℝ) := by ring
  rw [hevent]
  have hproxySum :
      (((∑ i, (weight i / 2) ^ 2 : ℝ≥0) : ℝ)) =
        (∑ i, (weight i : ℝ) ^ 2) / 4 := by
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hproxySum] at htail
  apply htail.trans_eq
  congr 1
  ring

/-- A fixed one-dimensional Gaussian activation packet. -/
def gaussianIntervalActivation (x : ℝ) : ℝ :=
  (Icc (1 : ℝ) 2).indicator (fun _ => 1) x

/-- Exact activation probability of the packet `[1,2]`. -/
def gaussianIntervalActivationMass : ℝ :=
  (gaussianReal 0 1).real (Icc (1 : ℝ) 2)

theorem gaussianIntervalActivationMass_pos :
    0 < gaussianIntervalActivationMass := by
  unfold gaussianIntervalActivationMass Measure.real
  exact ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num)).ne'
    (measure_ne_top _ _)

theorem gaussianIntervalActivation_measurable :
    Measurable gaussianIntervalActivation := by
  unfold gaussianIntervalActivation
  exact Measurable.indicator measurable_const measurableSet_Icc

theorem gaussianIntervalActivation_mem_Icc (x : ℝ) :
    gaussianIntervalActivation x ∈ Icc (0 : ℝ) 1 := by
  unfold gaussianIntervalActivation
  by_cases hx : x ∈ Icc (1 : ℝ) 2 <;> simp [hx]

theorem integral_gaussianIntervalActivation :
    ∫ x, gaussianIntervalActivation x ∂gaussianReal 0 1 =
      gaussianIntervalActivationMass := by
  unfold gaussianIntervalActivation
  rw [integral_indicator measurableSet_Icc]
  rw [integral_const]
  simp [gaussianIntervalActivationMass, Measure.real]

/-- **Stable-rank Gaussian quadratic lower tail.**  A weighted diagonal
Gaussian quadratic form falls below a fixed fraction of its trace with
probability exponentially small in `trace² / Frobenius²`.  No minimum weight,
rank, or determinant enters the estimate. -/
theorem measure_pi_gaussian_weighted_sq_sum_le
    {I : Type*} [Fintype I] (weight : I → ℝ≥0)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real
        {x | ∑ i, (weight i : ℝ) * x i ^ 2 ≤
          θ * ∑ i, (weight i : ℝ)} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i, (weight i : ℝ)) ^ 2 /
          ∑ i, (weight i : ℝ) ^ 2) := by
  let B : I → (I → ℝ) → ℝ :=
    fun i x => gaussianIntervalActivation (x i)
  have hindep : iIndepFun B (Measure.pi fun _ : I => gaussianReal 0 1) := by
    exact iIndepFun_pi fun _ => gaussianIntervalActivation_measurable.aemeasurable
  have hmeas : ∀ i, AEMeasurable (B i)
      (Measure.pi fun _ : I => gaussianReal 0 1) := by
    intro i
    exact (gaussianIntervalActivation_measurable.comp
      (measurable_pi_apply i)).aemeasurable
  have hbound : ∀ i, ∀ᵐ x ∂(Measure.pi fun _ : I => gaussianReal 0 1),
      B i x ∈ Icc (0 : ℝ) 1 := by
    intro i
    exact Filter.Eventually.of_forall fun x =>
      gaussianIntervalActivation_mem_Icc (x i)
  have hmean : ∀ i, ∫ x, B i x
      ∂(Measure.pi fun _ : I => gaussianReal 0 1) =
        gaussianIntervalActivationMass := by
    intro i
    rw [MeasureTheory.integral_comp_eval
      gaussianIntervalActivation_measurable.aestronglyMeasurable]
    exact integral_gaussianIntervalActivation
  have hbern := measure_weightedBernoulli_sum_le_of_iIndepFun
    hindep hmeas hbound hmean hθ weight
  apply (measureReal_mono ?_).trans hbern
  intro x hx
  have hpoint : ∀ i, gaussianIntervalActivation (x i) ≤ x i ^ 2 := by
    intro i
    unfold gaussianIntervalActivation
    by_cases hi : x i ∈ Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hi]
      have hi1 : (1 : ℝ) ≤ x i := hi.1
      have himul : (1 : ℝ) * 1 ≤ x i * x i :=
        mul_self_le_mul_self (by norm_num) hi1
      simpa [pow_two] using himul
    · rw [Set.indicator_of_notMem hi]
      positivity
  have hsum : ∑ i, (weight i : ℝ) * gaussianIntervalActivation (x i) ≤
      ∑ i, (weight i : ℝ) * x i ^ 2 := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hpoint i) (weight i).coe_nonneg
  exact hsum.trans hx

/-- Half-activation specialization with a universal positive threshold and
the clean exponent `-p² stableRank / 2`. -/
theorem measure_pi_gaussian_weighted_sq_sum_le_halfActivation
    {I : Type*} [Fintype I] (weight : I → ℝ≥0) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real
        {x | ∑ i, (weight i : ℝ) * x i ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i, (weight i : ℝ)} ≤
      Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          ((∑ i, (weight i : ℝ)) ^ 2 /
            ∑ i, (weight i : ℝ) ^ 2)) := by
  have h := measure_pi_gaussian_weighted_sq_sum_le weight
    (θ := gaussianIntervalActivationMass / 2)
    (by linarith [gaussianIntervalActivationMass_pos])
  apply h.trans_eq
  congr 1
  ring

/-- A complete finite family pays only its cardinality once every member has
the same stable-rank floor.  This is the circuit-union compiler replacing a
minimum singular-value or pseudodeterminant hypothesis. -/
theorem measure_pi_gaussian_iUnion_weighted_sq_sum_le_halfActivation
    {I C : Type*} [Fintype I] [Fintype C]
    (weight : C → I → ℝ≥0) (stableFloor : ℝ)
    (hstable : ∀ c,
      stableFloor ≤
        (∑ i, (weight c i : ℝ)) ^ 2 /
          ∑ i, (weight c i : ℝ) ^ 2) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real
        (⋃ c, {x | ∑ i, (weight c i : ℝ) * x i ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i, (weight c i : ℝ)}) ≤
      (Fintype.card C : ℝ) *
        Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
  calc
    (Measure.pi fun _ : I => gaussianReal 0 1).real
        (⋃ c, {x | ∑ i, (weight c i : ℝ) * x i ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i, (weight c i : ℝ)}) ≤
      ∑ c, (Measure.pi fun _ : I => gaussianReal 0 1).real
        {x | ∑ i, (weight c i : ℝ) * x i ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i, (weight c i : ℝ)} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : C,
        Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      apply Finset.sum_le_sum
      intro c _
      refine (measure_pi_gaussian_weighted_sq_sum_le_halfActivation
        (weight c)).trans ?_
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hstable c)
        (neg_nonpos.mpr (by positivity))
    _ = (Fintype.card C : ℝ) *
        Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      simp

end

end GaloisForLFunctions.HTGeometry
