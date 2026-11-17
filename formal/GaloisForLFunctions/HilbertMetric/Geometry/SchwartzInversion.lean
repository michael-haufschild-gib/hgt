import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Tactic

/-!
# Smooth flat extension of Schwartz functions through inversion

The chain rule is closed on Schwartz functions: its inverse-square factor
becomes a polynomial in the inverted coordinate. A quadratic decay bound
gives the derivative at the origin, and this closure proves every order of
smoothness and flatness without separate higher chain-rule estimates.
-/

open Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversion
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Inversion pullback with the smooth value selected by rapid decay. -/
def kelvin (f : SchwartzMap ℂ F) (z : ℂ) : F := if z = 0 then 0 else f z⁻¹

@[simp] theorem kelvin_zero (f : SchwartzMap ℂ F) : kelvin f 0 = 0 := by
  simp [kelvin]

theorem kelvin_of_ne_zero (f : SchwartzMap ℂ F) {z : ℂ} (hz : z ≠ 0) :
    kelvin f z = f z⁻¹ := if_neg hz

private def inverseFactor (w : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ (-(w ^ 2))

private theorem inverseFactor_hasTemperateGrowth : Function.HasTemperateGrowth inverseFactor := by
  unfold inverseFactor
  fun_prop

/-- The derivative before inversion is still Schwartz: only a polynomial multiplier is added. -/
def kelvinDerivative (f : SchwartzMap ℂ F) : SchwartzMap ℂ (ℂ →L[ℝ] F) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.compL ℝ ℂ ℂ F)
    inverseFactor_hasTemperateGrowth (SchwartzMap.fderivCLM ℝ ℂ F f)

theorem kelvinDerivative_apply (f : SchwartzMap ℂ F) (w : ℂ) :
    kelvinDerivative f w = (fderiv ℝ f w).comp (inverseFactor w) := rfl

/-- A single Schwartz seminorm provides the quadratic remainder at the origin. -/
theorem kelvin_quadratic_bound (f : SchwartzMap ℂ F) (z : ℂ) :
    ‖kelvin f z‖ ≤ SchwartzMap.seminorm ℝ 2 0 f * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · simp only [hz, kelvin_zero, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
  · rw [kelvin_of_ne_zero f hz]
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have h := f.norm_pow_mul_le_seminorm ℝ 2 z⁻¹
    rw [norm_inv] at h
    calc
      ‖f z⁻¹‖ = ‖z‖ ^ 2 * ((‖z‖⁻¹) ^ 2 * ‖f z⁻¹‖) := by field_simp
      _ ≤ ‖z‖ ^ 2 * SchwartzMap.seminorm ℝ 2 0 f :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := mul_comm _ _

theorem kelvin_hasFDerivAt_zero (f : SchwartzMap ℂ F) :
    HasFDerivAt (kelvin f) (0 : ℂ →L[ℝ] F) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  simp only [kelvin_zero, zero_apply, sub_zero]
  have hb (z : ℂ) : ‖z‖⁻¹ * ‖kelvin f z‖ ≤ SchwartzMap.seminorm ℝ 2 0 f * ‖z‖ := by
    by_cases hz : z = 0
    · simp only [hz, norm_zero, inv_zero, zero_mul, mul_zero, le_refl]
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      calc
        _ ≤ ‖z‖⁻¹ * (SchwartzMap.seminorm ℝ 2 0 f * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (kelvin_quadratic_bound f z) (inv_nonneg.mpr (norm_nonneg _))
        _ = _ := by field_simp
  apply squeeze_zero' (Eventually.of_forall (fun z => mul_nonneg (by positivity) (norm_nonneg _)))
    (Eventually.of_forall hb)
  simpa only [norm_zero, mul_zero] using
    (tendsto_const_nhds.mul (continuous_norm.tendsto (0 : ℂ)))

private theorem inversion_hasFDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ => w⁻¹) (inverseFactor z⁻¹) z := by
  have h : HasFDerivAt (fun w : ℂ => w⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)).restrictScalars ℝ) z :=
    (hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ
  have he : inverseFactor z⁻¹ =
      (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)).restrictScalars ℝ := by
    ext w
    change -(z⁻¹ ^ 2) * w = w * (-(z ^ 2)⁻¹)
    rw [inv_pow]
    ring
  rw [he]
  exact h

/-- The full derivative, including the removable singularity, is another inversion pullback. -/
theorem kelvin_hasFDerivAt (f : SchwartzMap ℂ F) (z : ℂ) :
    HasFDerivAt (kelvin f) (kelvin (kelvinDerivative f) z) z := by
  by_cases hz : z = 0
  · subst z
    rw [kelvin_zero]
    exact kelvin_hasFDerivAt_zero f
  · have he : kelvin f =ᶠ[𝓝 z] (fun w : ℂ => f w⁻¹) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact kelvin_of_ne_zero f hw
    rw [kelvin_of_ne_zero (kelvinDerivative f) hz, kelvinDerivative_apply]
    exact he.hasFDerivAt_iff.mpr ((f.hasFDerivAt z⁻¹).comp z (inversion_hasFDerivAt hz))

theorem fderiv_kelvin (f : SchwartzMap ℂ F) :
    fderiv ℝ (kelvin f) = kelvin (kelvinDerivative f) :=
  funext fun z => (kelvin_hasFDerivAt f z).fderiv

private theorem kelvin_contDiff_nat (n : ℕ) (f : SchwartzMap ℂ F) :
    ContDiff ℝ n (kelvin f) := by
  induction n generalizing F with
  | zero =>
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun z => (kelvin_hasFDerivAt f z).continuousAt))
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_fderiv]
      refine ⟨fun z => (kelvin_hasFDerivAt f z).differentiableAt, by simp, ?_⟩
      rw [fderiv_kelvin]
      exact ih (kelvinDerivative f)

/-- Every Schwartz function extends smoothly through complex inversion. -/
theorem kelvin_contDiff (f : SchwartzMap ℂ F) : ContDiff ℝ (∞ : ℕ∞ω) (kelvin f) := by
  exact contDiff_infty.mpr (fun n => kelvin_contDiff_nat n f)

/-- The extension is flat: every Fréchet derivative at the origin is zero. -/
theorem kelvin_iteratedFDeriv_zero (n : ℕ) (f : SchwartzMap ℂ F) :
    iteratedFDeriv ℝ n (kelvin f) 0 = 0 := by
  induction n generalizing F with
  | zero =>
      apply norm_eq_zero.mp
      rw [norm_iteratedFDeriv_zero, kelvin_zero, norm_zero]
  | succ n ih =>
      apply norm_eq_zero.mp
      rw [← norm_iteratedFDeriv_fderiv, fderiv_kelvin, ih (kelvinDerivative f), norm_zero]

private def northFactor (z : ℂ) : ℝ := ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2)

private theorem northFactor_contDiff : ContDiff ℝ (∞ : ℕ∞ω) northFactor := by
  exact (contDiff_norm_sq ℂ).div (contDiff_const.add (contDiff_norm_sq ℂ))
    (fun z => (by positivity : (1 : ℝ) + ‖z‖ ^ 2 ≠ 0))

/-- The correction in the chart centered at the missing stereographic pole. -/
def northCorrection (f : SchwartzMap ℂ ℝ) (z : ℂ) : ℝ := northFactor z * kelvin f z

theorem northCorrection_contDiff (f : SchwartzMap ℂ ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (northCorrection f) :=
  northFactor_contDiff.mul (kelvin_contDiff f)

/-- Stereographic weighting preserves the infinite-order agreement with the round sphere. -/
theorem northCorrection_iteratedFDeriv_zero (f : SchwartzMap ℂ ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (northCorrection f) 0 = 0 := by
  have hb := norm_iteratedFDeriv_mul_le northFactor_contDiff (kelvin_contDiff f) (0 : ℂ)
    (n := n) (by exact_mod_cast le_top)
  simp only [kelvin_iteratedFDeriv_zero, norm_zero, mul_zero, Finset.sum_const_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

def southSupport (f : SchwartzMap ℂ ℝ) (ε : ℝ) (w : ℂ) : ℝ :=
  1 + ε * f w / (1 + ‖w‖ ^ 2)

def northSupport (f : SchwartzMap ℂ ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  1 + ε * northCorrection f z

/-- The two explicit support-function formulas agree on their actual chart overlap. -/
theorem support_chart_overlap (f : SchwartzMap ℂ ℝ) (ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    southSupport f ε z⁻¹ = northSupport f ε z := by
  unfold southSupport northSupport northCorrection northFactor
  rw [kelvin_of_ne_zero f hz, norm_inv]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have hi : 1 + (‖z‖⁻¹) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem northSupport_contDiff (f : SchwartzMap ℂ ℝ) (ε : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (northSupport f ε) :=
  contDiff_const.add (contDiff_const.mul (northCorrection_contDiff f))

#print axioms kelvin_hasFDerivAt
#print axioms kelvin_contDiff
#print axioms kelvin_iteratedFDeriv_zero
#print axioms northCorrection_iteratedFDeriv_zero
#print axioms support_chart_overlap
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversion
