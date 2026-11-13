import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Integrals controlled by exponential distribution tails

Layer cake converts exponential bounds on superlevel measures into an
integral bound and a quantitative tail bound. No finite total measure is
required.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry

/-- An exponential superlevel bound controls the integral of a nonnegative function. -/
theorem lintegral_le_of_exponential_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {X : α → ℝ} (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x)
    {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 ≤ t → μ {x | t < X x} ≤
      ENNReal.ofReal (C * Real.exp (-(t / 2)))) :
    (∫⁻ x, ENNReal.ofReal (X x) ∂μ) ≤ ENNReal.ofReal (2 * C) := by
  have he : (fun t : ℝ => Real.exp (-(t / 2))) =
      (fun t => Real.exp ((-1 / 2 : ℝ) * t)) := by
    funext t
    congr 1
    ring
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(t / 2))) (Ioi 0) := by
    rw [he]
    exact integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0
  have hval : (∫ t in Ioi (0 : ℝ), C * Real.exp (-(t / 2))) = 2 * C := by
    rw [integral_const_mul, he, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0)]
    norm_num
    ring
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hX0) hX.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-(t / 2))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htail t ht.le
    _ = ENNReal.ofReal (2 * C) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul C)
        (Eventually.of_forall fun t => mul_nonneg hC (Real.exp_pos _).le), hval]

/-- The integral above height `T` decays as `(T+2) exp(-T/2)`. -/
theorem lintegral_tail_le_of_exponential_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {X : α → ℝ} (hX : Measurable X)
    {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 ≤ t → μ {x | t < X x} ≤
      ENNReal.ofReal (C * Real.exp (-(t / 2))))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ x in {x | T < X x}, ENNReal.ofReal (X x) ∂μ) ≤
      ENNReal.ofReal (C * (T + 2) * Real.exp (-(T / 2))) := by
  classical
  let S : Set α := {x | T < X x}
  let Y : α → ℝ := fun x => max (X x - T) 0
  have hS : MeasurableSet S := measurableSet_lt measurable_const hX
  have hY : Measurable Y := (hX.sub measurable_const).max measurable_const
  have hcoef : 0 ≤ C * Real.exp (-(T / 2)) := mul_nonneg hC (Real.exp_pos _).le
  have hYtail : ∀ s : ℝ, 0 ≤ s → μ {x | s < Y x} ≤
      ENNReal.ofReal ((C * Real.exp (-(T / 2))) * Real.exp (-(s / 2))) := by
    intro s hs
    have he : {x | s < Y x} = {x | T + s < X x} := by
      ext x
      simp only [Y, mem_setOf_eq, lt_max_iff, not_lt_of_ge hs, or_false]
      constructor <;> intro hx <;> linarith only [hx]
    rw [he]
    refine (htail (T + s) (add_nonneg hT hs)).trans_eq ?_
    congr 1
    rw [show -((T + s) / 2) = -(T / 2) + -(s / 2) by ring, Real.exp_add]
    ring
  have hYi := lintegral_le_of_exponential_tail μ hY (fun x => le_max_right _ _) hcoef hYtail
  -- Above `T`, the function splits into height `T` and its positive excess.
  have he (x : α) : S.indicator (fun x => ENNReal.ofReal (X x)) x =
      S.indicator (fun _ => ENNReal.ofReal T) x + ENNReal.ofReal (Y x) := by
    by_cases hx : x ∈ S
    · have hxT : T < X x := hx
      rw [indicator_of_mem hx, indicator_of_mem hx]
      dsimp only [Y]
      rw [max_eq_left (sub_nonneg.mpr hxT.le),
        ← ENNReal.ofReal_add hT (sub_nonneg.mpr hxT.le)]
      congr 1
      ring
    · have hxT : X x ≤ T := le_of_not_gt hx
      rw [indicator_of_notMem hx, indicator_of_notMem hx]
      simp only [Y, max_eq_right (sub_nonpos.mpr hxT), ENNReal.ofReal_zero, zero_add]
  calc
    _ = ∫⁻ x, S.indicator (fun x => ENNReal.ofReal (X x)) x ∂μ :=
      (lintegral_indicator hS (fun x => ENNReal.ofReal (X x))).symm
    _ = ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal T) x + ENNReal.ofReal (Y x) ∂μ :=
      lintegral_congr he
    _ = ENNReal.ofReal T * μ S + ∫⁻ x, ENNReal.ofReal (Y x) ∂μ := by
      rw [lintegral_add_left (measurable_const.indicator hS), lintegral_indicator hS,
        lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal T * ENNReal.ofReal (C * Real.exp (-(T / 2))) +
        ENNReal.ofReal (2 * (C * Real.exp (-(T / 2)))) :=
      add_le_add (mul_le_mul_right (htail T hT) (ENNReal.ofReal T)) hYi
    _ = _ := by
      rw [← ENNReal.ofReal_mul hT,
        ← ENNReal.ofReal_add (mul_nonneg hT hcoef) (mul_nonneg (by norm_num) hcoef)]
      congr 1
      ring

#print axioms lintegral_le_of_exponential_tail
#print axioms lintegral_tail_le_of_exponential_tail
end GaloisForLFunctions.HTGeometry
