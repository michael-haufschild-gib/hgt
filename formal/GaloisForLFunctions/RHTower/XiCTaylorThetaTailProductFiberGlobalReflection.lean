import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberGlobalCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierXi

/-!
# Boundary reflection value of the global theta-density phase

The real part of the positive-half-line phase of the exact density is not an independent Hardy
datum.  On the real spectral boundary it is determined exactly by `XiC`; only the odd sine/Hilbert
channel remains outside this reflection identity.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

lemma integrableOn_thetaCuspFullSource_mul_cos (t : ℝ) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFullSource x * Real.cos (t * x)) (Ioi 0) := by
  rw [show (fun x : ℝ => thetaCuspFullSource x * Real.cos (t * x)) =
      fun x : ℝ =>
        Real.cos (t * x) * thetaCuspTailDerivative 2 x -
          (1 / 4 : ℝ) * (Real.cos (t * x) * thetaCuspTailDerivative 0 x) by
    funext x
    rw [thetaCuspFullSource_eq_tail_second_sub]
    ring]
  exact (integrableOn_cos_mul_thetaCuspTailDerivative 2 t).sub
    ((integrableOn_cos_mul_thetaCuspTailDerivative 0 t).const_mul (1 / 4 : ℝ))

theorem thetaCuspTailSecondDensityPhaseValue_re_ofReal_eq_cosine
    (t : ℝ) :
    (thetaCuspTailSecondDensityPhaseValue (t : ℂ)).re =
      ∫ x : ℝ in Ioi 0,
        thetaCuspTailSecondDensity x * Real.cos (t * x) := by
  have hint := integrableOn_thetaCuspTailSecondDensity_mul_phase
    (z := (t : ℂ)) (by simp)
  unfold thetaCuspTailSecondDensityPhaseValue
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          spectralTranslationPhase x (t : ℂ)).re =
        ∫ x : ℝ in Ioi 0,
          ((thetaCuspTailSecondDensity x : ℂ) *
            spectralTranslationPhase x (t : ℂ)).re :=
      (integral_re hint).symm
    _ = ∫ x : ℝ in Ioi 0,
        thetaCuspTailSecondDensity x * Real.cos (t * x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hphaseRe : (spectralTranslationPhase x (t : ℂ)).re =
          Real.cos (x * t) := by
        unfold spectralTranslationPhase
        rw [show (x : ℂ) * I * (t : ℂ) = ((x * t : ℝ) : ℂ) * I by
          push_cast
          ring]
        exact Complex.exp_ofReal_mul_I_re (x * t)
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hphaseRe]
      congr 1
      ring

theorem integral_thetaCuspTailSecondDensity_mul_cos_eq_tail_add_fullSource
    (t : ℝ) :
    (∫ x : ℝ in Ioi 0,
      thetaCuspTailSecondDensity x * Real.cos (t * x)) =
      (∫ x : ℝ in Ioi 0,
        thetaCuspTailDerivative 0 x * Real.cos (t * x)) +
        4 * ∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (t * x) := by
  rw [show (fun x : ℝ =>
      thetaCuspTailSecondDensity x * Real.cos (t * x)) =
      fun x : ℝ =>
        thetaCuspTailDerivative 0 x * Real.cos (t * x) +
          4 * (thetaCuspFullSource x * Real.cos (t * x)) by
    funext x
    rw [thetaCuspTailSecondDensity_eq_tail_add_four_fullSource]
    ring]
  rw [integral_add]
  · rw [integral_const_mul]
  · have hI := integrableOn_cos_mul_thetaCuspTailDerivative 0 t
    simp only [mul_comm] at hI ⊢
    exact hI
  · exact (integrableOn_thetaCuspFullSource_mul_cos t).const_mul 4

/-- **Exact boundary reflection value relation.**  The even boundary channel of the full canonical
density phase is an elementary affine multiplier of `XiC`. -/
theorem thetaCuspTailSecondDensityPhaseValue_re_ofReal_crossed
    (t : ℝ) :
    (t ^ (2 : ℕ) + 1 / 4) *
        (thetaCuspTailSecondDensityPhaseValue (t : ℂ)).re =
      1 / 4 + 2 * t ^ (2 : ℕ) * (XiC (t : ℂ)).re := by
  let A : ℝ := ∫ x : ℝ in Ioi 0,
    thetaCuspTailDerivative 0 x * Real.cos (t * x)
  let B : ℝ := ∫ x : ℝ in Ioi 0,
    thetaCuspFullSource x * Real.cos (t * x)
  let R : ℝ := (thetaCuspTailSecondDensityPhaseValue (t : ℂ)).re
  let X : ℝ := (XiC (t : ℂ)).re
  have hR : R = A + 4 * B := by
    dsimp only [R, A, B]
    rw [thetaCuspTailSecondDensityPhaseValue_re_ofReal_eq_cosine,
      integral_thetaCuspTailSecondDensity_mul_cos_eq_tail_add_fullSource]
  have hB : B = 1 / 4 - (t ^ (2 : ℕ) + 1 / 4) * A := by
    dsimp only [B, A]
    exact integral_Ioi_thetaCuspFullSource_mul_cos t
  have hX : X = 2 * B := by
    dsimp only [X, B]
    rw [XiC_ofReal_eq_two_mul_thetaCuspCosine]
    norm_num
  dsimp only [R, X] at hR hX ⊢
  linear_combination (t ^ (2 : ℕ) + 1 / 4) * hR - 2 * t ^ (2 : ℕ) * hX + hB

end

end RHTower
