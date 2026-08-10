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

open Filter Topology MeasureTheory

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

/-! ## The one-step limit -/

/-- **Equation (10), for a family of amplitudes.**  Only common decay constants for the two
intermediate stages are required; the amplitude itself may move with the index.  This is the form
the iteration needs, because the amplitude produced by one step depends on `n` through `δ_n`. -/
theorem tendsto_gaussOneStep_powFamily {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop)
    (f : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    {A₁ A₂ θ : ℝ} (hθ : 1 / 2 < θ)
    (h1 : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((gaussPrimeScaleBlock hp (f n) : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ A₁ / (1 + (j.natAbs : ℝ)) ^ θ)
    (h2 : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
          (gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleBlock hp (f n))) : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ A₂ / (1 + (j.natAbs : ℝ)) ^ θ) :
    Tendsto (fun n : ℕ =>
      ‖gaussQuasiInnerG hm k p (fourierMulBlock (ι n) (f n)) -
        (((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (ι n)) * gaussSampleValue k p (ι n))) •
          fourierMulBlock (ι n)
            (gaussMovingAmplitudeBlock hp
              ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (f n))‖)
      atTop (nhds 0) := by
  have hM := gaussSampleValueBound_nonneg hm k p
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hE1 : Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockOf hm k p (ι n) (gaussPrimeScaleBlock hp (f n)) -
        gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (f n))‖) atTop (nhds 0) := by
    have h := tendsto_norm_gaussShiftedBlockOf_sub_rotation_powFamily hm k p hι
      (fun n : ℕ => gaussPrimeScaleBlock hp (f n)) hθ h1
    refine h.congr fun n => ?_
    rw [gaussRotationBlock_eq_translation]
  have hE2 : Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockDiag hm k p (ι n)
          (gaussPrimeScaleInvSqBlock hp
            (gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
              (gaussPrimeScaleBlock hp (f n)))) -
        gaussTranslationBlock (-((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)))
          (gaussPrimeScaleInvSqBlock hp
            (gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
              (gaussPrimeScaleBlock hp (f n))))‖) atTop (nhds 0) := by
    have h := tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv_powFamily hm k p hι
      (fun n : ℕ => gaussPrimeScaleInvSqBlock hp
        (gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (f n)))) hθ h2
    refine h.congr fun n => ?_
    rw [gaussRotationBlockInv_eq_translation]
  have hdom : Tendsto (fun n : ℕ =>
      Real.sqrt (p : ℝ) * ((p : ℝ) * gaussSampleValueBound hm k p *
          gaussSampleValueBound hm k p *
        (‖gaussShiftedBlockOf hm k p (ι n) (gaussPrimeScaleBlock hp (f n)) -
            gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
              (gaussPrimeScaleBlock hp (f n))‖ +
          ‖gaussShiftedBlockDiag hm k p (ι n)
              (gaussPrimeScaleInvSqBlock hp
                (gaussTranslationBlock
                  ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
                  (gaussPrimeScaleBlock hp (f n)))) -
            gaussTranslationBlock (-((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)))
              (gaussPrimeScaleInvSqBlock hp
                (gaussTranslationBlock
                  ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
                  (gaussPrimeScaleBlock hp (f n))))‖))) atTop (nhds 0) := by
    have hsum := hE1.add hE2
    rw [add_zero] at hsum
    have := (hsum.const_mul ((p : ℝ) * gaussSampleValueBound hm k p *
      gaussSampleValueBound hm k p)).const_mul (Real.sqrt (p : ℝ))
    simpa using this
  refine squeeze_zero_norm' ?_ hdom
  filter_upwards [hι.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : ι n ≠ 0 := by
    have hpos : 0 < (ι n).natAbs := hn
    omega
  have hbound := norm_gaussQuasiInnerG_sub_movingAmplitude_le hm k p hp hn0 (f n)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine hbound.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hd := norm_gaussSampleValue_le hm k p (ι n)
  have hfac : (p : ℝ) * ‖gaussSampleValue k p (ι n)‖ * gaussSampleValueBound hm k p
      ≤ (p : ℝ) * gaussSampleValueBound hm k p * gaussSampleValueBound hm k p := by
    have h1' : (p : ℝ) * ‖gaussSampleValue k p (ι n)‖
        ≤ (p : ℝ) * gaussSampleValueBound hm k p :=
      mul_le_mul_of_nonneg_left hd hppos.le
    exact mul_le_mul_of_nonneg_right h1' hM
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right hfac (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hfac (norm_nonneg _))

/-- **Equation (10), for a family of amplitudes**, at decay exponent one. -/
theorem tendsto_gaussOneStep_family {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop)
    (f : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    {A₁ A₂ : ℝ}
    (h1 : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((gaussPrimeScaleBlock hp (f n) : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ A₁ / (1 + (j.natAbs : ℝ)))
    (h2 : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
          (gaussTranslationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleBlock hp (f n))) : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ A₂ / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun n : ℕ =>
      ‖gaussQuasiInnerG hm k p (fourierMulBlock (ι n) (f n)) -
        (((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (ι n)) * gaussSampleValue k p (ι n))) •
          fourierMulBlock (ι n)
            (gaussMovingAmplitudeBlock hp
              ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (f n))‖)
      atTop (nhds 0) :=
  tendsto_gaussOneStep_powFamily hm k p hp hι f (A₁ := A₁) (A₂ := A₂) (θ := 1) (by norm_num)
    (fun n j => by rw [Real.rpow_one]; exact h1 n j)
    (fun n j => by rw [Real.rpow_one]; exact h2 n j)

/-- **Equation (10).**  For an amplitude whose two intermediate stages carry decay constants, the
quasi-inner block acts on the twisted amplitude as multiplication by the moving amplitude, up to an
`L²` error that vanishes. -/
theorem tendsto_gaussOneStep {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A₁ A₂ : ℝ}
    (h1 : ∀ j : ℤ,
      ‖fourierCoeff ((gaussPrimeScaleBlock hp f : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ A₁ / (1 + (j.natAbs : ℝ)))
    (h2 : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
          (gaussTranslationBlock ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleBlock hp f)) : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ A₂ / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun n : ℕ =>
      ‖gaussQuasiInnerG hm k p (fourierMulBlock (n : ℤ) f) -
        (((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (n : ℤ)) * gaussSampleValue k p (n : ℤ))) •
          fourierMulBlock (n : ℤ)
            (gaussMovingAmplitudeBlock hp
              ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) f)‖)
      atTop (nhds 0) :=
  tendsto_gaussOneStep_family hm k p hp (ι := fun n : ℕ => (n : ℤ))
    (by simp only [Int.natAbs_natCast]; exact Filter.tendsto_id) (fun _ => f)
    (fun _ j => h1 j) h2

end

end RHTower
