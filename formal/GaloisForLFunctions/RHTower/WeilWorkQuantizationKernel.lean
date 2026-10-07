import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shrinking Poisson windows

An arctangent difference integrates the Poisson kernel over a finite interval.
Uniform inverse-square decay permits passage to the boundary against measures
whose inverse-square moment is finite.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace RHTower.WeilSpectral

/-- Poisson mass of an interval, with the normalization giving limit `π` inside. -/
def intervalPhaseKernel (η a b r : ℝ) : ℝ :=
  Real.arctan ((b - r) / η) - Real.arctan ((a - r) / η)

theorem continuous_intervalPhaseKernel (η a b : ℝ) :
    Continuous (intervalPhaseKernel η a b) := by
  unfold intervalPhaseKernel
  fun_prop

theorem intervalPhaseKernel_nonneg {η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) (r : ℝ) :
    0 ≤ intervalPhaseKernel η a b r := by
  exact sub_nonneg.mpr (Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hab r) hη.le))

theorem intervalPhaseKernel_le_pi (η a b r : ℝ) :
    intervalPhaseKernel η a b r ≤ Real.pi := by
  unfold intervalPhaseKernel
  linarith [Real.arctan_lt_pi_div_two ((b - r) / η),
    Real.neg_pi_div_two_lt_arctan ((a - r) / η)]

theorem integral_poisson_interval {η : ℝ} (hη : 0 < η) (a b r : ℝ) :
    ∫ t in a..b, η / (η ^ 2 + (r - t) ^ 2) = intervalPhaseKernel η a b r := by
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t => Real.arctan ((t - r) / η))
        (η / (η ^ 2 + (r - t) ^ 2)) t := by
    intro t _
    have h := (Real.hasDerivAt_arctan ((t - r) / η)).comp t
      (((hasDerivAt_id t).sub_const r).div_const η)
    refine h.congr_deriv ?_
    field_simp
    ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.div (by fun_prop) (fun t => by positivity) :
      Continuous fun t : ℝ => η / (η ^ 2 + (r - t) ^ 2)).intervalIntegrable _ _)

/-- A uniform integrable bound for all Poisson widths at most one. -/
theorem intervalPhaseKernel_le_weight {η a b : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hab : a ≤ b) (r : ℝ) :
    intervalPhaseKernel η a b r ≤
      (Real.pi * (1 + 4 * (|a| + |b| + 1) ^ 2) + 8 * (b - a)) * (1 + r ^ 2)⁻¹ := by
  set R : ℝ := |a| + |b| + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg a, abs_nonneg b]
  have hden : 0 < 1 + r ^ 2 := by positivity
  by_cases hr : |r| ≤ 2 * R
  · have hrsq : r ^ 2 ≤ 4 * R ^ 2 := by
      have := sq_le_sq₀ (abs_nonneg r) (by linarith : 0 ≤ 2 * R) |>.mpr hr
      norm_num [sq_abs, mul_pow] at this ⊢
      exact this
    apply (intervalPhaseKernel_le_pi η a b r).trans
    rw [← div_eq_mul_inv, le_div_iff₀ hden]
    nlinarith [Real.pi_pos]
  · have hrR : 2 * R < |r| := lt_of_not_ge hr
    have hr1 : 1 ≤ r ^ 2 := by
      have : 1 ≤ |r| := by linarith
      nlinarith [sq_abs r]
    have hbound : ∀ t ∈ Icc a b,
        η / (η ^ 2 + (r - t) ^ 2) ≤ 8 / (1 + r ^ 2) := by
      intro t ht
      have htR : |t| ≤ R := by
        rw [abs_le]
        dsimp [R]
        constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, abs_nonneg a,
          abs_nonneg b, ht.1, ht.2]
      have hrt : |r| ≤ |r - t| + |t| := by
        simpa using abs_add_le (r - t) t
      have hsq : r ^ 2 ≤ 4 * (r - t) ^ 2 := by
        have hhalf : |r| ≤ 2 * |r - t| := by linarith
        have := sq_le_sq₀ (abs_nonneg r) (by positivity : 0 ≤ 2 * |r - t|) |>.mpr hhalf
        norm_num [sq_abs, mul_pow] at this ⊢
        exact this
      have hpos : 0 < η ^ 2 + (r - t) ^ 2 := by positivity
      rw [div_le_div_iff₀ hpos hden]
      nlinarith [sq_nonneg η, mul_le_mul_of_nonneg_right hη1 hden.le]
    have hint : IntervalIntegrable (fun t : ℝ => η / (η ^ 2 + (r - t) ^ 2)) volume a b :=
      (continuous_const.div (by fun_prop) (fun t => by positivity) :
        Continuous fun t : ℝ => η / (η ^ 2 + (r - t) ^ 2)).intervalIntegrable _ _
    have h := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hbound
    rw [integral_poisson_interval hη, intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    refine h.trans ?_
    rw [div_eq_mul_inv]
    have hp : 0 ≤ Real.pi * (1 + 4 * R ^ 2) := by positivity
    have hi : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
    nlinarith [mul_nonneg hp hi]

theorem tendsto_arctan_div_pos {x : ℝ} (hx : 0 < x) :
    Tendsto (fun η : ℝ => Real.arctan (x / η)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
  simpa only [div_eq_mul_inv, Function.comp_def] using
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_inv_nhdsGT_zero.const_mul_atTop hx)

theorem tendsto_arctan_div_neg {x : ℝ} (hx : x < 0) :
    Tendsto (fun η : ℝ => Real.arctan (x / η)) (𝓝[>] 0) (𝓝 (-(Real.pi / 2))) := by
  simpa only [neg_div, Real.arctan_neg, neg_neg] using
    (tendsto_arctan_div_pos (neg_pos.mpr hx)).neg

/-- Away from the endpoints a shrinking Poisson window tends to the interval indicator. -/
theorem tendsto_intervalPhaseKernel {a b r : ℝ} (hab : a < b) (hra : r ≠ a) (hrb : r ≠ b) :
    Tendsto (fun η => intervalPhaseKernel η a b r) (𝓝[>] 0)
      (𝓝 ((Ioc a b).indicator (fun _ => Real.pi) r)) := by
  rcases lt_or_gt_of_ne hra with hra | hra
  · have hrb' : r < b := hra.trans hab
    have h := (tendsto_arctan_div_pos (sub_pos.mpr hrb')).sub
      (tendsto_arctan_div_pos (sub_pos.mpr hra))
    simpa [intervalPhaseKernel, not_lt.mpr hra.le] using h
  · rcases lt_or_gt_of_ne hrb with hrb | hrb
    · have h := (tendsto_arctan_div_pos (sub_pos.mpr hrb)).sub
        (tendsto_arctan_div_neg (sub_neg.mpr hra))
      convert h using 1 <;> simp [intervalPhaseKernel, hra, hrb.le]
    · have h := (tendsto_arctan_div_neg (sub_neg.mpr hrb)).sub
        (tendsto_arctan_div_neg (sub_neg.mpr (hab.trans hrb)))
      simpa [intervalPhaseKernel, not_le.mpr hrb] using h

/-- Stieltjes inversion with only an inverse-square moment and null interval endpoints. -/
theorem tendsto_integral_intervalPhaseKernel {μ : Measure ℝ}
    (hμ : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ) {a b : ℝ} (hab : a < b)
    (ha : μ {a} = 0) (hb : μ {b} = 0) :
    Tendsto (fun η => ∫ r, intervalPhaseKernel η a b r ∂μ) (𝓝[>] 0)
      (𝓝 (Real.pi * μ.real (Ioc a b))) := by
  let C : ℝ := Real.pi * (1 + 4 * (|a| + |b| + 1) ^ 2) + 8 * (b - a)
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ᵐ r ∂μ,
      ‖intervalPhaseKernel η a b r‖ ≤ C * (1 + r ^ 2)⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with η hη
    exact Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalPhaseKernel_nonneg hη.1 hab.le r)]
      exact intervalPhaseKernel_le_weight hη.1 hη.2.le hab.le r
  have haeA : ∀ᵐ r ∂μ, r ≠ a := by simpa only [ae_iff, not_not, setOf_eq_eq_singleton] using ha
  have haeB : ∀ᵐ r ∂μ, r ≠ b := by simpa only [ae_iff, not_not, setOf_eq_eq_singleton] using hb
  have hlim : ∀ᵐ r ∂μ, Tendsto (fun η => intervalPhaseKernel η a b r) (𝓝[>] 0)
      (𝓝 ((Ioc a b).indicator (fun _ => Real.pi) r)) := by
    filter_upwards [haeA, haeB] with r hra hrb
    exact tendsto_intervalPhaseKernel hab hra hrb
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun r => C * (1 + r ^ 2)⁻¹)
    (Eventually.of_forall fun η => (continuous_intervalPhaseKernel η a b).aestronglyMeasurable)
    hbound (hμ.const_mul C) hlim
  simpa [integral_indicator measurableSet_Ioc, integral_const, measureReal_def,
    Measure.restrict_apply, smul_eq_mul, mul_comm] using h

end RHTower.WeilSpectral
