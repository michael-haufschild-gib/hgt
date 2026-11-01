import GaloisForLFunctions.HTGeometry.AffineExpanders.QuadraticBound
import GaloisForLFunctions.HTGeometry.FiniteZeroSumSpectral
import GaloisForLFunctions.HTGeometry.ConstitutiveRecoveryCocycleHolonomy

/-!
# Uniform contraction of the Margulis–Gabber–Galil walk

The native symmetric bistochastic kernel contracts fluctuations about `finiteMean`
by `5√2/8`, uniformly over moduli at least three.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace GaloisForLFunctions.HTGeometry
section FixedModulus
variable {n : ℕ} [NeZero n]

/-- The MGG walk contracts every zero-sum function uniformly in the modulus. -/
theorem mggAffine_norm_le (hn : 3 ≤ n) (f : EuclideanSpace ℝ (ZMod n × ZMod n))
    (hf : ∑ a, f a = 0) :
    ‖Matrix.toEuclideanLin (mggAffineKernel n).val f‖ ≤
      (5 * Real.sqrt 2 / 8) * ‖f‖ :=
  bistochastic_zeroSum_norm_le (mggAffineKernel n) (mggAffineMatrix_symm n)
    (5 * Real.sqrt 2 / 8) (by positivity) (mggAffineMatrix_quadratic_le hn) f hf

/-- One MGG step contracts the fluctuation about the existing finite-mean functional. -/
theorem mggAffine_centered_norm_le (hn : 3 ≤ n) (f : ZMod n × ZMod n → ℝ) :
    ‖WithLp.toLp 2 (fun a => ((mggAffineKernel n).val *ᵥ f) a - finiteMean f)‖ ≤
      (5 * Real.sqrt 2 / 8) *
        ‖WithLp.toLp 2 (fun a => f a - finiteMean f)‖ := by
  let g : EuclideanSpace ℝ (ZMod n × ZMod n) :=
    WithLp.toLp 2 (fun a => f a - finiteMean f)
  have hg : ∑ a, g a = 0 := sum_sub_finiteMean_eq_zero f
  have heq : Matrix.toEuclideanLin (mggAffineKernel n).val g =
      WithLp.toLp 2 (fun a => ((mggAffineKernel n).val *ᵥ f) a - finiteMean f) := by
    ext a
    change ((mggAffineKernel n).val *ᵥ (fun a => f a - finiteMean f)) a = _
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    change _ - (∑ b, mggAffineMatrix n a b) * finiteMean f = _
    rw [mggAffineMatrix_row, one_mul]
  simpa only [heq] using mggAffine_norm_le hn g hg

end FixedModulus

/-- The eight affine transitions have a uniform nonconstant spectral radius below one. -/
theorem mggAffine_expander_family (n : ℕ)
    (f : ZMod (n + 3) × ZMod (n + 3) → ℝ) :
    (‖WithLp.toLp 2 (fun a => ((mggAffineKernel (n + 3)).val *ᵥ f) a - finiteMean f)‖ ≤
      (5 * Real.sqrt 2 / 8) *
        ‖WithLp.toLp 2 (fun a => f a - finiteMean f)‖) ∧
      5 * Real.sqrt 2 / 8 < 1 := by
  refine ⟨mggAffine_centered_norm_le (by omega) f, ?_⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [hs, Real.sqrt_nonneg 2]

end GaloisForLFunctions.HTGeometry
