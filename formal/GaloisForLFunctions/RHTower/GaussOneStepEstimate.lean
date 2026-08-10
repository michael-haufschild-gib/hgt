import GaloisForLFunctions.RHTower.GaussStepScalarTaming
import GaloisForLFunctions.RHTower.GaussMovingAmplitudeOperator

/-!
# The one-step estimate

Combining the exact factorization, the telescoping identity and the two taming bounds gives the
error of the card's equation (10) as a sum of two moving-translation errors:

`‖G(e_n f) - (p |d_n|²) e_n (a_(δ_n) f)‖
    ≤ √p ( p |d_n| M ‖S*(Bf) - T_(δ_n)(Bf)‖ + p |d_n|² ‖S(w') - T_(δ_n)^(-1)(w')‖ )`,

where `w' = B^(-2) T_(δ_n) (B f)`.  Both errors are exactly what the uniform moving-translation
estimates send to zero, and neither is divided by `d_n`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

theorem gaussShiftedBlockDiag_sub {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussShiftedBlockDiag hm k p n u - gaussShiftedBlockDiag hm k p n v
      = gaussShiftedBlockDiag hm k p n (u - v) := by
  rw [gaussShiftedBlockDiag, gaussShiftedBlockDiag, gaussShiftedBlockDiag]
  simp only [map_sub, smul_sub]

/-- **The one-step error bound.**  The deviation of `G` from the moving amplitude is bounded by the
two moving-translation errors, with no division by `d_n`. -/
theorem norm_gaussQuasiInnerG_sub_movingAmplitude_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖gaussQuasiInnerG hm k p (fourierMulBlock n f) -
        (((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) •
          fourierMulBlock n
            (gaussMovingAmplitudeBlock hp
              ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) f)‖
      ≤ Real.sqrt (p : ℝ) *
        ((p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p *
            ‖gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp f) -
              gaussTranslationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                (gaussPrimeScaleBlock hp f)‖ +
          (p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p *
            ‖gaussShiftedBlockDiag hm k p n
                (gaussPrimeScaleInvSqBlock hp
                  (gaussTranslationBlock
                    ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                    (gaussPrimeScaleBlock hp f))) -
              gaussTranslationBlock (-((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)))
                (gaussPrimeScaleInvSqBlock hp
                  (gaussTranslationBlock
                    ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
                    (gaussPrimeScaleBlock hp f)))‖) := by
  set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) with hδ
  set σ : ℂ := ((p : ℝ) : ℂ) *
    (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n) with hσ
  set Bf : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp f with hBf
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p n Bf) with hw
  set w' : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp (gaussTranslationBlock δ Bf) with hw'
  -- the two exact identities
  have hfact := gaussQuasiInnerG_fourierMulBlock hm k p hp hn f
  rw [← hσ, ← hBf, ← hw] at hfact
  have htel := gaussPrimeScaleBlock_translate_invSq_translate hp δ f
  rw [← hBf, ← hw'] at htel
  -- rewrite both sides
  have hrewrite :
      gaussQuasiInnerG hm k p (fourierMulBlock n f) -
          σ • fourierMulBlock n (gaussMovingAmplitudeBlock hp δ f)
        = fourierMulBlock n
            (gaussPrimeScaleBlock hp
              (σ • gaussShiftedBlockDiag hm k p n w -
                σ • gaussTranslationBlock (-δ) w')) := by
    rw [hfact, ← htel, ← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_sub, ← map_sub]
  rw [hrewrite]
  refine le_trans (norm_fourierMulBlock_apply_le n _) ?_
  refine le_trans ((gaussPrimeScaleBlock hp).le_opNorm _) ?_
  refine le_trans (mul_le_mul_of_nonneg_right (norm_gaussPrimeScaleBlock_le hp)
    (norm_nonneg _)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hsplit : σ • gaussShiftedBlockDiag hm k p n w - σ • gaussTranslationBlock (-δ) w'
      = σ • gaussShiftedBlockDiag hm k p n (w - w')
        + (σ • gaussShiftedBlockDiag hm k p n w' - σ • gaussTranslationBlock (-δ) w') := by
    rw [← gaussShiftedBlockDiag_sub, smul_sub]
    abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · -- first error: the moving-translation error of the conjugate block, tamed
    refine le_trans (norm_smul_gaussShiftedBlockDiag_le hm k p hn (w - w')) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
        (gaussSampleValueBound_nonneg hm k p))
    rw [hw, hw', ← map_sub]
    refine le_trans ((gaussPrimeScaleInvSqBlock hp).le_opNorm _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (norm_gaussPrimeScaleInvSqBlock_le hp)
      (norm_nonneg _)) ?_
    rw [one_mul]
  · -- second error: the moving-translation error of the unconjugated block
    rw [← smul_sub, norm_smul, hσ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < (p : ℝ)), RCLike.norm_conj]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hd := norm_gaussSampleValue_le hm k p n
    have hnn : (0 : ℝ) ≤ (p : ℝ) * ‖gaussSampleValue k p n‖ := by positivity
    calc (p : ℝ) * (‖gaussSampleValue k p n‖ * ‖gaussSampleValue k p n‖)
        = (p : ℝ) * ‖gaussSampleValue k p n‖ * ‖gaussSampleValue k p n‖ := by ring
      _ ≤ (p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p :=
          mul_le_mul_of_nonneg_left hd hnn

end

end RHTower
