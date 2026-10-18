import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Compact smoothing preserves a fixed exponential envelope, including the
first derivative. No faster-than-every-exponential premise is needed. -/

open MeasureTheory Set
open scoped Convolution
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def expWeightedKernelMass (κ : ℝ → ℝ) : ℝ := ∫ y : ℝ, |κ y| * Real.exp |y|

theorem expWeightedKernelMass_nonneg (κ : ℝ → ℝ) : 0 ≤ expWeightedKernelMass κ :=
  integral_nonneg fun y => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem integrable_expWeightedKernel {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) : Integrable (fun y : ℝ => |κ y| * Real.exp |y|) := by
  have hc : Continuous (fun y : ℝ => |κ y| * Real.exp |y|) :=
    hκ.abs.mul (Real.continuous_exp.comp continuous_abs)
  exact hc.integrable_of_hasCompactSupport
    (hκc.comp_left (show |(0 : ℝ)| = 0 from abs_zero)).mul_right

private theorem exp_abs_shift (x y : ℝ) :
    Real.exp (-|x-y|) ≤ Real.exp |y| * Real.exp (-|x|) := by
  have ht : |x| ≤ |x-y|+|y| := by
    simpa only [sub_add_cancel] using (_root_.abs_add_le (x-y) y)
  calc
    _ ≤ Real.exp (|y|+-|x|) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_add _ _

/-- An explicit weighted kernel mass controls the smoothed source envelope. -/
theorem compactConvolution_exp_bound {f κ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, |f x| ≤ C*Real.exp (-|x|)) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (x : ℝ) :
    |(κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x| ≤
      C*expWeightedKernelMass κ*Real.exp (-|x|) := by
  have hm := (integrable_expWeightedKernel hκ hκc).mul_const (C*Real.exp (-|x|))
  have hb : ∀ᵐ y : ℝ, ‖κ y*f (x-y)‖ ≤
      (|κ y| * Real.exp |y|)*(C*Real.exp (-|x|)) := by
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ |κ y| * (C*Real.exp (-|x-y|)) :=
        mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
      _ ≤ |κ y| * (C*(Real.exp |y| * Real.exp (-|x|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_abs_shift x y) hC)
          (abs_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫ y : ℝ, (|κ y| * Real.exp |y|)*(C*Real.exp (-|x|)) := by
      simpa only [convolution_def, ContinuousLinearMap.mul_apply', Real.norm_eq_abs] using
        norm_integral_le_of_norm_le hm hb
    _ = _ := by
      rw [integral_mul_const]
      unfold expWeightedKernelMass
      ring

/-- The common value-and-derivative envelope is produced by moving the
derivative to the compact kernel. -/
theorem compactConvolution_contDiff_exp_bounds {f κ : ℝ → ℝ} {C : ℝ}
    (hfi : Integrable f) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C*Real.exp (-|x|))
    (hκ : ContDiff ℝ 2 κ) (hκc : HasCompactSupport κ) :
    ContDiff ℝ 2 (κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
        |(κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x| ≤ D*Real.exp (-|x|) ∧
        |deriv (κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x| ≤ D*Real.exp (-|x|) := by
  have hκd : Continuous (deriv κ) := hκ.continuous_deriv (by norm_num)
  have hm := expWeightedKernelMass_nonneg κ
  have hmd := expWeightedKernelMass_nonneg (deriv κ)
  refine ⟨hκc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hκ hfi.locallyIntegrable,
    C*(expWeightedKernelMass κ+expWeightedKernelMass (deriv κ)),
    mul_nonneg hC (add_nonneg hm hmd), fun x => ⟨?_, ?_⟩⟩
  · exact (compactConvolution_exp_bound hC hf hκ.continuous hκc x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hmd]) hC)
        (Real.exp_pos _).le)
  · rw [(hκc.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
      (hκ.of_le (by norm_num)) hfi.locallyIntegrable x).deriv]
    exact (compactConvolution_exp_bound hC hf hκd hκc.deriv x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hm]) hC)
        (Real.exp_pos _).le)

/-- Exponential tilting commutes with convolution by an exact product rule. -/
theorem exponential_tilt_convolution (κ f : ℝ → ℝ) (z : ℂ) :
    (fun x : ℝ => Complex.exp (z*(x : ℂ))*
      ((κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x : ℂ)) =
      (fun x : ℝ => Complex.exp (z*(x : ℂ))*(κ x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun x : ℝ => Complex.exp (z*(x : ℂ))*(f x : ℂ)) := by
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Complex.ofReal_mul]
  have he : Complex.exp (z*(x : ℂ)) =
      Complex.exp (z*(y : ℂ))*Complex.exp (z*((x-y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Fubini supplies both integrability and the normalized transform product. -/
theorem integral_exponential_tilt_convolution {κ f : ℝ → ℝ} (z : ℂ)
    (hκ : Integrable (fun x : ℝ => Complex.exp (z*(x : ℂ))*(κ x : ℂ)))
    (hf : Integrable (fun x : ℝ => Complex.exp (z*(x : ℂ))*(f x : ℂ))) :
    Integrable (fun x : ℝ => Complex.exp (z*(x : ℂ))*
      ((κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x : ℂ)) ∧
    (∫ x : ℝ, Complex.exp (z*(x : ℂ))*((κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x : ℂ)) =
      (∫ x : ℝ, Complex.exp (z*(x : ℂ))*(κ x : ℂ))*
        (∫ x : ℝ, Complex.exp (z*(x : ℂ))*(f x : ℂ)) := by
  rw [exponential_tilt_convolution]
  exact ⟨hκ.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hκ hf⟩

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
