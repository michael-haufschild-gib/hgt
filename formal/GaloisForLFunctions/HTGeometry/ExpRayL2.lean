import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The exponential kernel on a ray

The kernel `x ↦ exp (-w x)` of the half-line Laplace transform, on a ray `(T, ∞)` and for
`Re w > 0`: its modulus, its integrability, its total mass and its square mass.  These are the
elementary facts behind the Paley--Wiener description of the Hardy space of a half-plane.

## Main results

* `integral_exp_neg_mul_Ioi`
* `norm_exp_neg_mul_ofReal`
* `integral_norm_sq_expRay`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

noncomputable section

/-- A decaying exponential tends to zero along the ray. -/
theorem tendsto_exp_neg_mul_atTop_nhds_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun y : ℝ => Real.exp (-(b * y))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => b * y) atTop atTop := by
    simpa using tendsto_id.const_mul_atTop hb
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)

/-- A decaying exponential is integrable on every ray. -/
theorem integrableOn_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) (T : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(b * x))) (Ioi T) := by
  have h := exp_neg_integrableOn_Ioi T hb
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [neg_mul]

/-- The total mass of a decaying exponential on a ray. -/
theorem integral_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) (T : ℝ) :
    (∫ x in Ioi T, Real.exp (-(b * x))) = Real.exp (-(b * T)) / b := by
  have hderiv : ∀ x ∈ Ioi T, HasDerivAt (fun y : ℝ => -Real.exp (-(b * y)) / b)
      (Real.exp (-(b * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(b * y)) (-b) x := by
      simpa [neg_mul] using (hasDerivAt_id x).const_mul (-b)
    refine ((h1.exp).neg.div_const b).congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt (fun y : ℝ => -Real.exp (-(b * y)) / b) (Ici T) T := by
    fun_prop
  have hlim : Tendsto (fun y : ℝ => -Real.exp (-(b * y)) / b) atTop (𝓝 0) := by
    simpa using ((tendsto_exp_neg_mul_atTop_nhds_zero hb).neg.div_const b)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_exp_neg_mul_Ioi hb T) hlim
  rw [h]
  ring

/-! ### The complex exponential ray kernel -/

/-- The exponential kernel of the half-line Laplace transform. -/
def expRay (w : ℂ) (x : ℝ) : ℂ := Complex.exp (-(w * (x : ℝ)))

theorem norm_expRay (w : ℂ) (x : ℝ) : ‖expRay w x‖ = Real.exp (-(w.re * x)) := by
  rw [expRay, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem continuous_expRay (w : ℂ) : Continuous (expRay w) := by
  unfold expRay
  fun_prop

theorem norm_sq_expRay (w : ℂ) (x : ℝ) : ‖expRay w x‖ ^ 2 = Real.exp (-(2 * w.re * x)) := by
  rw [norm_expRay, ← Real.exp_nat_mul]
  congr 1
  ring

theorem integrableOn_norm_sq_expRay {w : ℂ} (hw : 0 < w.re) (T : ℝ) :
    IntegrableOn (fun x : ℝ => ‖expRay w x‖ ^ 2) (Ioi T) := by
  have h2 : (0 : ℝ) < 2 * w.re := by linarith
  refine (integrableOn_exp_neg_mul_Ioi h2 T).congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [norm_sq_expRay]

/-- The square mass of the exponential kernel on a ray. -/
theorem integral_norm_sq_expRay {w : ℂ} (hw : 0 < w.re) (T : ℝ) :
    (∫ x in Ioi T, ‖expRay w x‖ ^ 2) = Real.exp (-(2 * w.re * T)) / (2 * w.re) := by
  have h2 : (0 : ℝ) < 2 * w.re := by linarith
  rw [← integral_exp_neg_mul_Ioi h2 T]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [norm_sq_expRay]

theorem memLp_two_expRay_restrict {w : ℂ} (hw : 0 < w.re) (T : ℝ) :
    MemLp (expRay w) 2 (volume.restrict (Ioi T)) := by
  refine (memLp_two_iff_integrable_sq_norm ?_).2 (integrableOn_norm_sq_expRay hw T)
  exact (continuous_expRay w).aestronglyMeasurable

/-- The `L²` mass of the exponential kernel on a ray, in root form. -/
theorem sqrt_integral_norm_sq_expRay {w : ℂ} (hw : 0 < w.re) (T : ℝ) :
    Real.sqrt (∫ x in Ioi T, ‖expRay w x‖ ^ 2)
      = Real.exp (-(w.re * T)) / Real.sqrt (2 * w.re) := by
  have h2 : (0 : ℝ) < 2 * w.re := by linarith
  have hnum : Real.sqrt (Real.exp (-(2 * w.re * T))) = Real.exp (-(w.re * T)) := by
    have hsplit : Real.exp (-(2 * w.re * T))
        = Real.exp (-(w.re * T)) * Real.exp (-(w.re * T)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [integral_norm_sq_expRay hw T, Real.sqrt_div (Real.exp_pos _).le, hnum]

end

end GaloisForLFunctions.HTGeometry
