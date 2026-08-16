import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielRawCenterMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielCenterMomentExplicit

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Raw mollified error with a universal leading constant. Pole clearing costs at most the square of
the explicit center-to-pole ratio; all remaining degeneration is the explicit moving-right factor. -/
theorem exists_inghamRawError_uniformGabrielCenterMoment_le_explicit :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      ∀ {X : ℕ}, 4 ≤ X →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
          inghamMollifier X
            ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
              inghamUniformGabrielInteriorPower sigma) ≤
        C *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hcenter⟩ :=
    exists_inghamGabrielPoleClearedError_uniformCenterMoment_le_explicit
  refine ⟨C0, hC0, ?_⟩
  intro sigma hsigma0 hsigma1 X hX
  have hc0 : 0 < inghamUniformGabrielCenter sigma :=
    lt_of_lt_of_le (by norm_num) (inghamUniformGabrielCenter_ge_half hsigma0)
  have hc1 : inghamUniformGabrielCenter sigma < 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter1 : inghamUniformGabrielCenter sigma ≠ 1 := hc1.ne
  let A : ℝ :=
    (1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1
  have hgap : 0 < 1 - inghamUniformGabrielCenter sigma := sub_pos.mpr hc1
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    exact one_le_mul_of_one_le_of_one_le
      (by
        have hinv : 0 ≤ 1 / (1 - inghamUniformGabrielCenter sigma) := by
          positivity
        linarith)
      (Real.one_le_exp (by norm_num))
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA1
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
          inghamUniformGabrielInteriorPower sigma
  let field : ℝ → ℝ := fun t =>
    ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
      ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖ ^
        inghamUniformGabrielInteriorPower sigma
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact (continuous_inghamRawError_uniformGabrielCenter
      sigma X hcenter1).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hfieldCont : Continuous field := by
    dsimp only [field]
    exact (continuous_poleCleared_vertical_of_half_le X
      (z := (inghamUniformGabrielCenter sigma : ℂ))
      (inghamUniformGabrielCenter_ge_half hsigma0)).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hpoint : ∀ t ∈ Icc (-(X : ℝ)) (X : ℝ),
      raw t ≤ A ^ inghamUniformGabrielInteriorPower sigma * field t := by
    intro t ht
    have hraw := norm_inghamRawError_uniformCenter_le_regularized X
      hc0 hc1 (kappa := 1) (T := (X : ℝ)) (t := t)
      (by norm_num) hXpos ((abs_le).2 ht)
    have hp := Real.rpow_le_rpow (norm_nonneg _) hraw
      (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at hp
    simpa only [raw, field, A] using hp
  have hintegral :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := by
    calc
      (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
          ∫ t in Icc (-(X : ℝ)) (X : ℝ),
            A ^ inghamUniformGabrielInteriorPower sigma * field t := by
        exact integral_mono_ae hrawCont.integrableOn_Icc
          ((continuous_const.mul hfieldCont).integrableOn_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
      _ = A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := by
        rw [MeasureTheory.integral_const_mul, inghamUniformGabrielCenterMoment]
  have hApow :
      A ^ inghamUniformGabrielInteriorPower sigma ≤ A ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le hA1
        (inghamUniformGabrielInteriorPower_le_two hsigma1le))
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := hintegral
    _ ≤ A ^ (2 : ℕ) *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) :=
      mul_le_mul_of_nonneg_right hApow
        (inghamUniformGabrielCenterMoment_nonneg _ _ _)
    _ ≤ A ^ (2 : ℕ) *
        (C0 *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hcenter hsigma0 hsigma1 hX) (sq_nonneg A)
    _ = C0 * A ^ (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by ring

end

end RHTower.Sieve
