import GaloisForLFunctions.HTGeometry.SchwartzWeightedHolder

/-!
# The Sobolev estimate for Schwartz functions

Multiplication by the coordinate on the Fourier side is differentiation on the original side, so
the quadratic weighting of a transform is the transform of a second-order differential expression:
`(1+t²)·𝓕f = 𝓕(f − f''/4π²)`.  Plancherel then turns the weighted `L²` norm of the transform into
the `L²` norm of that expression.

Combined with the bound of the supremum by the weighted `L²` norm of the transform this is the
Sobolev estimate: the supremum of a Schwartz function is bounded by a fixed multiple of the `L²`
norm of `f − f''/4π²`.

* `mulXCLM_fourierSCLM` : multiplication on the Fourier side is differentiation.
* `weightSchwartz_fourierSCLM` : **`(1+t²)·𝓕f = 𝓕(f − f''/4π²)`.**
* `norm_apply_le_sobolev` : **`‖f x‖ ≤ C · ‖f − f''/4π²‖₂`.**
-/

open scoped Real SchwartzMap FourierTransform
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- The second-order elliptic expression `f − f''/4π²`. -/
def sobolevOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) - ((4 * (π : ℂ) ^ 2)⁻¹) • (derivSCLM.comp derivSCLM)

theorem sobolevOp_apply (f : 𝓢(ℝ, ℂ)) :
    sobolevOp f = f - ((4 * (π : ℂ) ^ 2)⁻¹) • derivSCLM (derivSCLM f) := rfl

theorem two_pi_I_ne_zero : (2 * (π : ℂ) * I) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- **Multiplication by the coordinate on the Fourier side is differentiation.** -/
theorem mulXCLM_fourierSCLM (f : 𝓢(ℝ, ℂ)) :
    mulXCLM (fourierSCLM f) = ((2 * (π : ℂ) * I)⁻¹) • fourierSCLM (derivSCLM f) := by
  rw [fourierSCLM_derivSCLM, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

/-- **The quadratic weighting of a transform is the transform of the elliptic expression.** -/
theorem weightSchwartz_fourierSCLM (f : 𝓢(ℝ, ℂ)) :
    weightSchwartz (fourierSCLM f) = fourierSCLM (sobolevOp f) := by
  have hstep : mulXCLM (mulXCLM (fourierSCLM f))
      = ((2 * (π : ℂ) * I)⁻¹ * (2 * (π : ℂ) * I)⁻¹) • fourierSCLM (derivSCLM (derivSCLM f)) := by
    rw [mulXCLM_fourierSCLM, map_smul, mulXCLM_fourierSCLM, smul_smul]
  have hsq : ((2 * (π : ℂ) * I)⁻¹ * (2 * (π : ℂ) * I)⁻¹) = -((4 * (π : ℂ) ^ 2)⁻¹) := by
    have hI : I * I = -1 := Complex.I_mul_I
    rw [← mul_inv, ← inv_neg]
    congr 1
    calc (2 * (π : ℂ) * I) * (2 * (π : ℂ) * I) = 4 * (π : ℂ) ^ 2 * (I * I) := by ring
      _ = -(4 * (π : ℂ) ^ 2) := by rw [hI]; ring
  have hleft : weightSchwartz (fourierSCLM f)
      = fourierSCLM f + mulXCLM (mulXCLM (fourierSCLM f)) := by
    show fourierSCLM f + mulXCLM (mulXCLM (fourierSCLM f)) = _
    rfl
  rw [hleft, hstep, hsq, sobolevOp_apply, map_sub, map_smul, neg_smul, ← sub_eq_add_neg]

/-- **Plancherel turns the weighted `L²` norm of the transform into the `L²` norm of the elliptic
expression.** -/
theorem norm_weight_fourier_toLp (f : 𝓢(ℝ, ℂ)) :
    ‖(weightSchwartz (fourierSCLM f)).toLp 2 (volume : Measure ℝ)‖
      = ‖(sobolevOp f).toLp 2 (volume : Measure ℝ)‖ := by
  rw [weightSchwartz_fourierSCLM, fourierSCLM_eq]
  exact SchwartzMap.norm_fourier_toL2_eq (sobolevOp f)

/-- **The Sobolev estimate**: the supremum of a Schwartz function is bounded by a fixed multiple of
the `L²` norm of `f − f''/4π²`. -/
theorem norm_apply_le_sobolev (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖f x‖
      ≤ (∫ t : ℝ, ((1 + t ^ 2)⁻¹) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        * ‖(sobolevOp f).toLp 2 (volume : Measure ℝ)‖ := by
  have h := norm_apply_le_weight_fourier f x
  rwa [norm_weight_fourier_toLp] at h

end GaloisForLFunctions

end
