/-
# Chen--Gupta--Li normalized real smooth bump

The source cutoff is real, nonnegative, and bounded by one.  This closes the
finite Hilbert--Schmidt estimate used in CGL Proposition 4.6.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHZeroDyadicReindex
import GaloisForLFunctions.RHTower.ChenGuptaLiRealSmoothBump

noncomputable section

namespace RHTower

open Matrix

/-- A source-normalized real CGL cutoff. -/
structure CGLUnitRealSmoothBump extends CGLRealSmoothBump where
  norm_le_one : ∀ x, ‖toCGLSmoothBump.value x‖ ≤ 1

/-- The source dyadic cutoff weight has norm at most one at every matrix
column. -/
theorem cglUnitRealSmoothBump_dyadicWeight_norm_le_one
    (w : CGLUnitRealSmoothBump) (N : CGLPositiveLength) (j : Fin N.value) :
    ‖cglSmoothBumpDyadicWeight w.toCGLRealSmoothBump.toCGLSmoothBump N j‖ ≤ 1 := by
  exact w.norm_le_one _

/-- The normalized finite source column mass is at most the dyadic length. -/
theorem cglUnitRealSmoothBump_unitWeightMass_le_length
    (w : CGLUnitRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    cglSmoothBumpDyadicUnitWeightMass w.toCGLRealSmoothBump.toCGLSmoothBump N Q ≤ N.value := by
  unfold cglSmoothBumpDyadicUnitWeightMass
  calc
    ∑ j : Fin N.value,
        ‖cglSmoothBumpDyadicWeight w.toCGLRealSmoothBump.toCGLSmoothBump N j‖ ^ 2 *
          cglCharacterDyadicUnitSupport N.value Q.value j ≤ ∑ _j : Fin N.value, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hu : IsUnit (cglCharacterDyadicIndex N.value j : ZMod Q.value)
      · simp only [cglCharacterDyadicUnitSupport, if_pos hu, mul_one]
        have hn := cglUnitRealSmoothBump_dyadicWeight_norm_le_one w N j
        have hnonneg : 0 ≤ ‖cglSmoothBumpDyadicWeight
            w.toCGLRealSmoothBump.toCGLSmoothBump N j‖ := norm_nonneg _
        nlinarith [mul_nonneg (sub_nonneg.mpr hn)
          (add_nonneg hnonneg (by norm_num : (0 : ℝ) ≤ 1))]
      · simp [cglCharacterDyadicUnitSupport, hu]
    _ = N.value := by simp

/-- CGL's normalized Hilbert--Schmidt trace is at most `|W|N`. -/
theorem cglUnitRealSmoothBump_trace_self_mul_conjTranspose_re_le_card_mul_length
    (w : CGLUnitRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    ((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLRealSmoothBump.toCGLSmoothBump N) rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w.toCGLRealSmoothBump.toCGLSmoothBump N) rows)ᴴ).trace).re ≤
      R * N.value := by
  have htrace := congrArg Complex.re
    (cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_unitWeightMass
      N.value Q.value R (cglSmoothBumpDyadicWeight w.toCGLRealSmoothBump.toCGLSmoothBump N) rows)
  norm_num at htrace
  rw [htrace]
  exact mul_le_mul_of_nonneg_left (cglUnitRealSmoothBump_unitWeightMass_le_length w N Q)
    (Nat.cast_nonneg R)

end RHTower
