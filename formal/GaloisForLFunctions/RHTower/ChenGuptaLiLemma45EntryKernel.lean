/-
# Chen--Gupta--Li Lemma 4.5 entry kernel

This is the exact finite matrix-to-kernel normalization used before the three
affine Poisson transformations in CGL Lemma 4.5.  A real cutoff changes the
two matrix weights into `w²`, while the dyadic phase bridge changes the
remaining oscillation into the literal kernel `h_(t_r - t_s)(n / N)`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHtDyadicPhase
import GaloisForLFunctions.RHTower.ChenGuptaLiHZeroDyadicReindex
import GaloisForLFunctions.RHTower.ChenGuptaLiRealSmoothBump

open Complex

noncomputable section

namespace RHTower

/-- A real CGL matrix weight times a literal dyadic phase is the scale phase
times the normalized `h_t` kernel. -/
theorem cglRealSmoothBumpDyadicWeight_phase_eq_scale_mul_ht
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (t : ℝ) (j : Fin N.value) :
    cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j *
        (starRingEnd ℂ) (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j) *
          cglCharacterDyadicPhase N.value t j =
      cglMellinPhase t N.value * cglSmoothBumpHt w.toCGLSmoothBump t
        ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) := by
  have hstar : (starRingEnd ℂ)
      (w.toCGLSmoothBump.value ((cglCharacterDyadicIndex N.value j : ℝ) / N.value)) =
        w.toCGLSmoothBump.value ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) := by
    rw [w.value_eq_realValue]
    simp
  unfold cglSmoothBumpDyadicWeight
  rw [hstar, cglCharacterDyadicPhase_eq_mellinPhase_mul_scaled,
    cglSmoothBumpHt_apply, cglSmoothBumpHtValue]
  ring

/-- Every literal weighted CGL Gram entry is a scale phase times its exact
finite `h_(t_r-t_s)` character sum. -/
theorem cglCharacterDyadicWeightedCorrelation_eq_scale_mul_ht_sum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (q : ℕ)
    (r s : CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedCorrelation N.value q
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) r s =
      cglMellinPhase (r.time - s.time) N.value *
        ∑ j : Fin N.value,
          r.character (cglCharacterDyadicIndex N.value j) *
            (starRingEnd ℂ) (s.character (cglCharacterDyadicIndex N.value j)) *
              cglSmoothBumpHt w.toCGLSmoothBump (r.time - s.time)
                ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) := by
  unfold cglCharacterDyadicWeightedCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j *
          (starRingEnd ℂ) (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N j) *
            cglCharacterDyadicPhase N.value (r.time - s.time) j) *
          r.character (cglCharacterDyadicIndex N.value j) *
            (starRingEnd ℂ) (s.character (cglCharacterDyadicIndex N.value j)) := by ring
    _ = (cglMellinPhase (r.time - s.time) N.value *
          cglSmoothBumpHt w.toCGLSmoothBump (r.time - s.time)
            ((cglCharacterDyadicIndex N.value j : ℝ) / N.value)) *
          r.character (cglCharacterDyadicIndex N.value j) *
            (starRingEnd ℂ) (s.character (cglCharacterDyadicIndex N.value j)) := by
      rw [cglRealSmoothBumpDyadicWeight_phase_eq_scale_mul_ht]
    _ = _ := by ring

end RHTower
