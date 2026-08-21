import GaloisForLFunctions.RHTower.ChenGuptaLiHZeroTracePoisson

open Matrix
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- A CGL weighted character Gram trace has zero imaginary part. -/
theorem cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_im_eq_zero
    (N q R : ℕ) (weight : Fin N → ℂ) (rows : Fin R → CGLCharacterDyadicRowData q) :
    ((cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows)ᴴ).trace).im = 0 := by
  unfold Matrix.trace Matrix.diag
  simp_rw [Matrix.mul_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Matrix.conjTranspose_apply]
  change (cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows r j *
      (starRingEnd ℂ) (cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows r j)).im = 0
  rw [Complex.mul_conj]
  simp

/-- The CGL weighted character Gram trace is its real part embedded in `ℂ`. -/
theorem cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_ofReal_re
    (N q R : ℕ) (weight : Fin N → ℂ) (rows : Fin R → CGLCharacterDyadicRowData q) :
    (cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows)ᴴ).trace =
      (((cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N q R weight rows)ᴴ).trace).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_im_eq_zero]

/-- **CGL Lemma 4.4.** The literal finite CGL weighted character Gram trace equals its
reduced-residue Ramanujan/Fourier expansion for every certified real CGL cutoff. -/
theorem cglRealSmoothBumpDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_ramanujanFourier
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace =
      (R : ℂ) * ∑' ell : ℤ, cglRamanujanAdditiveSum Q (ell : ZMod Q.value) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (fun u => w.toCGLSmoothBump.value u * w.toCGLSmoothBump.value u)
            (cglAffineFourierScale N Q * (ell : ℝ))) := by
  rw [cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_ofReal_re]
  exact cglRealSmoothBumpDyadicWeighted_trace_re_ofReal_eq_card_mul_ramanujanFourier
    w N Q R rows

end RHTower
