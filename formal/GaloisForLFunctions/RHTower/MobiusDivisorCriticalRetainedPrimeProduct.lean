import GaloisForLFunctions.RHTower.MobiusDivisorCriticalRetainedPrimeBoundary
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Absolute product admission for the retained prime source

The finite prime cutoff is preserved while passing to counting measure.
Absolute integrability at the critical endpoint justifies Fubini for the
literal Abel source, before applying any prime dilation.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- A single retained prime atom, with its actual source and full damping. -/
def criticalRetainedPrimeSourceAtom (δ : ℝ) (p : ℕ) (y : ℝ) : ℝ :=
  if p.Prime ∧ (p : ℝ) ≤ y then
    criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * (p : ℝ)⁻¹ *
      Real.exp (-δ * (Real.log p + Real.log y))
  else 0

/-- The omitted old-prime atom with the literal square-root cutoff. -/
def criticalRetainedPrimeHeadAtom (p : ℕ) (x : ℝ) : ℝ :=
  if p.Prime ∧ (p : ℝ) ^ (2 : ℕ) ≤ x then
    Real.sqrt p * criticalContinuousAbel (x / p)
  else 0

private theorem retained_dilation_weight {p y : ℝ} (hp : 0 < p) (hy : 0 < y) (δ : ℝ) :
    p * (p * y) ^ (-(5 / 2 : ℝ) - δ) * Real.sqrt p =
      (y ^ (5 / 2 : ℝ))⁻¹ * p⁻¹ * Real.exp (-δ * (Real.log p + Real.log y)) := by
  have hcombine : p * (p * y) ^ (-(5 / 2 : ℝ) - δ) * Real.sqrt p =
      p ^ (-(1 : ℝ) - δ) * y ^ (-(5 / 2 : ℝ) - δ) := by
    rw [Real.mul_rpow hp.le hy.le, Real.sqrt_eq_rpow]
    calc
      _ = (p ^ (1 : ℝ) * p ^ (-(5 / 2 : ℝ) - δ) * p ^ (1 / 2 : ℝ)) *
          y ^ (-(5 / 2 : ℝ) - δ) := by rw [Real.rpow_one]; ring
      _ = _ := by
        rw [← Real.rpow_add hp, ← Real.rpow_add hp]
        congr 2
        ring
  rw [hcombine,
    show -(1 : ℝ) - δ = -(1 : ℝ) + -δ by ring,
    show -(5 / 2 : ℝ) - δ = -(5 / 2 : ℝ) + -δ by ring,
    Real.rpow_add hp, Real.rpow_add hy,
    Real.rpow_neg hp.le, Real.rpow_one, Real.rpow_neg hy.le,
    Real.rpow_def_of_pos hp (-δ), Real.rpow_def_of_pos hy (-δ)]
  rw [show -δ * (Real.log p + Real.log y) =
    Real.log p * -δ + Real.log y * -δ by ring, Real.exp_add]
  ring

/-- Exact source-level change of variables, including the retained cutoff
and the dilation Jacobian. It holds for every natural index. -/
theorem criticalRetainedPrimeSourceAtom_dilation (δ : ℝ) (p : ℕ) (y : ℝ) :
    criticalRetainedPrimeSourceAtom δ p y =
      (p : ℝ) * ((p : ℝ) * y) ^ (-(5 / 2 : ℝ) - δ) *
        criticalRetainedPrimeHeadAtom p ((p : ℝ) * y) := by
  by_cases hp : p.Prime
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    simp only [criticalRetainedPrimeSourceAtom, criticalRetainedPrimeHeadAtom,
      hp, true_and, pow_two, mul_le_mul_iff_right₀ hp0]
    split_ifs with hpy
    · have hy0 : 0 < y := hp0.trans_le hpy
      rw [mul_div_cancel_left₀ _ hp0.ne']
      calc
        _ = ((y ^ (5 / 2 : ℝ))⁻¹ * (p : ℝ)⁻¹ *
            Real.exp (-δ * (Real.log p + Real.log y))) * criticalContinuousAbel y := by ring
        _ = _ := by rw [← retained_dilation_weight hp0 hy0 δ]; ring
    · simp
  · simp [criticalRetainedPrimeSourceAtom, criticalRetainedPrimeHeadAtom, hp]

private theorem mem_retainedPrimeCutoff_iff {y : ℝ} (hy : 1 < y) (p : ℕ) :
    p ∈ retainedPrimeCutoff y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  simp only [retainedPrimeCutoff, Finset.mem_filter, Finset.mem_Icc,
    Nat.le_floor_iff (le_of_lt (lt_trans zero_lt_one hy))]
  constructor
  · rintro ⟨⟨_, hpy⟩, hp⟩
    exact ⟨hp, hpy⟩
  · rintro ⟨hp, hpy⟩
    exact ⟨⟨by have := hp.two_le; omega, hpy⟩, hp⟩

private theorem sourceAtom_zero_of_not_mem {δ y : ℝ} (hy : 1 < y) {p : ℕ}
    (hp : p ∉ retainedPrimeCutoff y) : criticalRetainedPrimeSourceAtom δ p y = 0 := by
  simp only [criticalRetainedPrimeSourceAtom, if_neg ((mem_retainedPrimeCutoff_iff hy p).not.mp hp)]

private theorem integral_count_eq_finite (f : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ p ∉ s, f p = 0) :
    Integrable f Measure.count ∧ (∫ p, f p ∂Measure.count) = ∑ p ∈ s, f p := by
  have hi : Integrable f Measure.count := integrable_count_iff.mpr
    (summable_of_ne_finset_zero (s := s) (fun p hp => by simp [hs p hp]))
  refine ⟨hi, ?_⟩
  rw [integral_countable hi]
  simp only [count_real_singleton, one_smul]
  exact tsum_eq_sum hs

private theorem sourceAtom_count_integrable {δ y : ℝ} (hy : 1 < y) :
    Integrable (fun p : ℕ => criticalRetainedPrimeSourceAtom δ p y) Measure.count :=
  (integral_count_eq_finite _ (retainedPrimeCutoff y)
    (fun _ hp => sourceAtom_zero_of_not_mem hy hp)).1

private theorem sourceAtom_count_integral {δ y : ℝ} (hy : 1 < y) :
    (∫ p : ℕ, criticalRetainedPrimeSourceAtom δ p y ∂Measure.count) =
      criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * retainedPrimeBoundaryKernel δ y := by
  rw [(integral_count_eq_finite _ (retainedPrimeCutoff y)
    (fun _ hp => sourceAtom_zero_of_not_mem hy hp)).2]
  rw [retainedPrimeBoundaryKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [criticalRetainedPrimeSourceAtom, if_pos ((mem_retainedPrimeCutoff_iff hy p).mp hp)]
  ring

private theorem sourceAtom_count_norm_integral {δ y : ℝ} (hy : 1 < y) :
    (∫ p : ℕ, ‖criticalRetainedPrimeSourceAtom δ p y‖ ∂Measure.count) =
      |criticalContinuousAbel y| / y ^ (5 / 2 : ℝ) * retainedPrimeBoundaryKernel δ y := by
  rw [(integral_count_eq_finite _ (retainedPrimeCutoff y)
    (fun _ hp => by rw [sourceAtom_zero_of_not_mem hy hp, norm_zero])).2]
  rw [retainedPrimeBoundaryKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [criticalRetainedPrimeSourceAtom, if_pos ((mem_retainedPrimeCutoff_iff hy p).mp hp)]
  have hr : 0 < y ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (lt_trans zero_lt_one hy) _
  have hi : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hr,
    abs_of_nonneg hi, abs_of_pos (Real.exp_pos _)]
  ring

private theorem measurable_sourceAtom (δ : ℝ) (p : ℕ) :
    Measurable (criticalRetainedPrimeSourceAtom δ p) := by
  change Measurable (fun y : ℝ => criticalRetainedPrimeSourceAtom δ p y)
  by_cases hp : p.Prime
  · simp only [criticalRetainedPrimeSourceAtom, hp, true_and]
    apply Measurable.ite measurableSet_Ici _ measurable_const
    apply ((measurable_criticalContinuousAbel.div
      (measurable_id.pow_const (5 / 2 : ℝ))).mul measurable_const).mul
    fun_prop
  · simp only [criticalRetainedPrimeSourceAtom, hp, false_and, if_false]
    exact measurable_const

/-- Absolute product integrability at and to the right of the critical
boundary, with counting measure retaining every actual prime atom. -/
theorem integrable_criticalRetainedPrimeSource_product {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun z : ℕ × ℝ => criticalRetainedPrimeSourceAtom δ z.1 z.2)
      (Measure.count.prod (volume.restrict (Ioi (1 : ℝ)))) := by
  have hm : Measurable (fun z : ℕ × ℝ => criticalRetainedPrimeSourceAtom δ z.1 z.2) :=
    measurable_from_prod_countable_right (measurable_sourceAtom δ)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact sourceAtom_count_integrable hy
  · apply IntegrableOn.congr_fun (integrableOn_criticalRetainedPrimeAbsoluteBoundary hδ)
      _ measurableSet_Ioi
    intro y hy
    exact (sourceAtom_count_norm_integral hy).symm

/-- Exact admitted prime expansion of the retained boundary transform. The
exchange follows from absolute product integrability, including at zero. -/
theorem criticalRetainedPrimeBoundaryTransform_eq_prime_integrals {δ : ℝ} (hδ : 0 ≤ δ) :
    criticalRetainedPrimeBoundaryTransform δ =
      ∑' p : ℕ, ∫ y in Ioi (1 : ℝ), criticalRetainedPrimeSourceAtom δ p y := by
  have hi := integrable_criticalRetainedPrimeSource_product hδ
  calc
    _ = ∫ y in Ioi (1 : ℝ), ∫ p : ℕ, criticalRetainedPrimeSourceAtom δ p y
        ∂Measure.count := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (sourceAtom_count_integral hy).symm
    _ = ∫ p : ℕ, (∫ y in Ioi (1 : ℝ), criticalRetainedPrimeSourceAtom δ p y)
        ∂Measure.count := (integral_integral_swap hi).symm
    _ = _ := by
      rw [integral_countable hi.integral_prod_left]
      simp only [count_real_singleton, one_smul]

end RHTower
