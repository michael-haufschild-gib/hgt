import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialTensorSector
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Rapid decay for every finite polynomial log-density

The finite polynomial sector is stable under positive rescaling and reflection. Its
exponentials dominate every polynomial amplitude on both tails, giving global weighted
bounds needed to turn tensor half-densities into actual Schwartz functions.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Positive real powers preserve the full finite polynomial sector. -/
def gomesFinitePolynomialScale (a : Set.Ioi (0 : ℝ))
    (P : GomesFinitePolynomialProfile) : GomesFinitePolynomialProfile :=
  ⟨C a.val * P.val, by
    change IsFiniteMeasure (gomesDilatonMeasure (C a.val * P.val))
    have hp := (gomesDilatonMeasure_finite_iff_integrable P.val).mp P.property
    rw [gomesPolynomialExponential_integrable_decay_iff] at hp
    rw [gomesDilatonMeasure_finite_iff_integrable, gomesPolynomialExponential_integrable_decay_iff]
    exact ⟨by simpa only [eval_mul, eval_C] using hp.1.const_mul_atBot a.property,
      by simpa only [eval_mul, eval_C] using hp.2.const_mul_atBot a.property⟩⟩

/-- Spatial reflection preserves the full finite polynomial sector. -/
def gomesFinitePolynomialReflect (P : GomesFinitePolynomialProfile) :
    GomesFinitePolynomialProfile :=
  ⟨P.val.comp (-X), by
    change IsFiniteMeasure (gomesDilatonMeasure (P.val.comp (-X)))
    have hp := (gomesDilatonMeasure_finite_iff_integrable P.val).mp P.property
    rw [gomesPolynomialExponential_integrable_decay_iff] at hp
    rw [gomesDilatonMeasure_finite_iff_integrable, gomesPolynomialExponential_integrable_decay_iff]
    exact ⟨by simpa only [Function.comp_def, eval_comp, eval_neg, eval_X] using
      hp.2.comp tendsto_neg_atTop_atBot,
      by simpa only [Function.comp_def, eval_comp, eval_neg, eval_X] using
        hp.1.comp tendsto_neg_atBot_atTop⟩⟩

/-- A decaying linear exponential defeats every polynomial amplitude. -/
theorem gomesPolynomialExp_negative_linear_tail (Q : ℝ[X]) :
    Tendsto (fun x : ℝ => Q.eval x * Real.exp (-x)) atTop (𝓝 0) := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
    simpa only [eval_add, add_mul, add_zero] using hQ.add hR
  | monomial n a =>
    simpa only [eval_monomial, mul_assoc, mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul a

/-- The same tail estimate holds at every positive exponential rate. -/
theorem gomesPolynomialExp_linear_tail (Q : ℝ[X]) (a : Set.Ioi (0 : ℝ)) :
    Tendsto (fun x : ℝ => Q.eval x * Real.exp (-a.val * x)) atTop (𝓝 0) := by
  have ha : a.val ≠ 0 := ne_of_gt a.property
  have ht := (gomesPolynomialExp_negative_linear_tail (Q.comp (C (a.val⁻¹) * X))).comp
    (tendsto_id.const_mul_atTop a.property)
  change Tendsto (fun x : ℝ => (Q.comp (C (a.val⁻¹) * X)).eval (a.val * x) *
    Real.exp (-(a.val * x))) atTop (𝓝 0) at ht
  have he : (fun x : ℝ => (Q.comp (C (a.val⁻¹) * X)).eval (a.val * x) *
      Real.exp (-(a.val * x))) = (fun x => Q.eval x * Real.exp (-a.val * x)) := by
    funext x
    rw [eval_comp, eval_mul, eval_C, eval_X]
    simp only [← mul_assoc, inv_mul_cancel₀ ha, one_mul, neg_mul]
  rw [he] at ht
  exact ht

/-- Every polynomial amplitude times a finite density vanishes on the right tail. -/
theorem gomesPolynomialExp_amplitude_atTop (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    Tendsto (fun x => |Q.eval x| * Real.exp (P.val.eval x)) atTop (𝓝 0) := by
  have hp := (gomesFinitePolynomialProfiles_mem_iff P.val).mp P.property
  obtain ⟨c, hc, henv⟩ := (gomesPolynomialExponential_linear_envelope_iff P.val).mpr ⟨hp.1, hp.2.2⟩
  let a : Set.Ioi (0 : ℝ) := ⟨-c, neg_pos.mpr hc⟩
  have hlim : Tendsto (fun x => |Q.eval x| * Real.exp (c * x)) atTop (𝓝 0) := by
    simpa only [a, neg_neg, abs_mul, abs_of_pos (Real.exp_pos _), abs_zero] using
      (gomesPolynomialExp_linear_tail Q a).abs
  apply squeeze_zero' (Eventually.of_forall (fun x => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
    _ hlim
  filter_upwards [henv] with x hx
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (abs_nonneg _)

/-- Reflection supplies the corresponding left-tail estimate. -/
theorem gomesPolynomialExp_amplitude_atBot (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    Tendsto (fun x => |Q.eval x| * Real.exp (P.val.eval x)) atBot (𝓝 0) := by
  simpa only [Function.comp_def, gomesFinitePolynomialReflect, eval_comp, eval_neg,
    eval_X, neg_neg] using
    (gomesPolynomialExp_amplitude_atTop (gomesFinitePolynomialReflect P) (Q.comp (-X))).comp
      tendsto_neg_atBot_atTop

/-- Polynomial amplitudes vanish at spatial infinity, with both tails controlled. -/
theorem gomesPolynomialExp_amplitude_cocompact (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    Tendsto (fun x => |Q.eval x| * Real.exp (P.val.eval x)) (cocompact ℝ) (𝓝 0) := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  exact ⟨gomesPolynomialExp_amplitude_atBot P Q, gomesPolynomialExp_amplitude_atTop P Q⟩

/-- Every polynomial amplitude admits a global bound against a finite density. -/
theorem gomesPolynomialExp_amplitude_bounded (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    ∃ C : ℝ, ∀ x, |Q.eval x| * Real.exp (P.val.eval x) ≤ C := by
  let f : ZeroAtInftyContinuousMap ℝ ℝ :=
    { toFun := fun x => |Q.eval x| * Real.exp (P.val.eval x)
      continuous_toFun := Q.continuous.abs.mul (Real.continuous_exp.comp P.val.continuous)
      zero_at_infty' := gomesPolynomialExp_amplitude_cocompact P Q }
  obtain ⟨C, hC⟩ := ZeroAtInftyContinuousMap.bounded f
  refine ⟨C + f 0, fun x => ?_⟩
  have hx := hC x 0
  rw [Real.dist_eq] at hx
  have hl := le_abs_self (f x - f 0)
  change f x ≤ C + f 0
  linarith

/-- Arbitrarily high spatial moments remain uniformly bounded. -/
theorem gomesPolynomialExp_weighted_bounded (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) (k : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖Q.eval x * Real.exp (P.val.eval x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := gomesPolynomialExp_amplitude_bounded P (X ^ k * Q)
  refine ⟨C, fun x => ?_⟩
  simpa only [eval_mul, eval_pow, eval_X, abs_mul, abs_pow, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_assoc] using hC x

end GaloisForLFunctions.HTGeometry
