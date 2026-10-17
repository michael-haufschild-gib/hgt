import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionAngleNorm

/-!
# Exact alternating-projection rate on arithmetic tent spaces

The common-range component is fixed, while the reduced product has a single
arithmetic decay factor. Every iterate has an exact operator-norm error.
-/

noncomputable section
open MeasureTheory Set

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem reducedCoprimeProduct_mul_lcm (d e : ℕ) :
    reducedCoprimeProduct d e * coprimeProjector (coprimeLcm d e) = 0 := by
  have hQ : coprimeProjector e * coprimeProjector (coprimeLcm d e) =
      coprimeProjector (coprimeLcm d e) := by
    rw [coprimeLcm_comm d e]
    exact coprimeProjector_mul_lcm e d
  simp only [reducedCoprimeProduct, sub_mul, mul_assoc, hQ,
    coprimeProjector_mul_lcm, coprimeProjector_mul_self, sub_self]

theorem coprimeLcmProjector_mul_product (d e : ℕ) :
    coprimeProjector (coprimeLcm d e) * (coprimeProjector d * coprimeProjector e) =
      coprimeProjector (coprimeLcm d e) := by
  rw [← mul_assoc, coprimeLcmProjector_mul, coprimeLcm_comm d e,
    coprimeLcmProjector_mul]

theorem reducedCoprimeProduct_mul_product (d e : ℕ) :
    reducedCoprimeProduct d e * (coprimeProjector d * coprimeProjector e) =
      coprimeAngleSquare d e • reducedCoprimeProduct d e := by
  have h : coprimeProjector d * coprimeProjector e =
      reducedCoprimeProduct d e + coprimeProjector (coprimeLcm d e) := by
    simp only [reducedCoprimeProduct, sub_add_cancel]
  rw [h, mul_add, reducedCoprimeProduct_square, reducedCoprimeProduct_mul_lcm, add_zero]

/-- Every positive iterate has an exact reduced-product expression. -/
theorem coprime_alternating_projection_exact (d e k : ℕ) :
    (coprimeProjector d * coprimeProjector e) ^ (k + 1) -
        coprimeProjector (coprimeLcm d e) =
      coprimeAngleSquare d e ^ k • reducedCoprimeProduct d e := by
  induction k with
  | zero => simp only [zero_add, pow_one, pow_zero, one_smul, reducedCoprimeProduct]
  | succ k ih =>
    have hpow : (coprimeProjector d * coprimeProjector e) ^ (k + 1) =
        coprimeAngleSquare d e ^ k • reducedCoprimeProduct d e +
          coprimeProjector (coprimeLcm d e) := by
      rw [← ih, sub_add_cancel]
    rw [pow_succ _ (k + 1), hpow, add_mul, smul_mul_assoc,
      reducedCoprimeProduct_mul_product, coprimeLcmProjector_mul_product,
      add_sub_cancel_right, smul_smul, pow_succ]

/-- Sharp squared norm of every alternating-projection error, for all spacings. -/
theorem norm_sq_coprime_alternating_projection (d e k : ℕ) :
    ‖(coprimeProjector d * coprimeProjector e) ^ (k + 1) -
        coprimeProjector (coprimeLcm d e)‖ ^ 2 =
      coprimeAngleSquare d e ^ (2 * k + 1) := by
  rw [coprime_alternating_projection_exact, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, norm_sq_reducedCoprimeProduct, ← pow_mul, ← pow_succ]
  congr 1
  omega

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
