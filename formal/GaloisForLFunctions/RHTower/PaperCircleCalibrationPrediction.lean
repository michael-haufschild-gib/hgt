import GaloisForLFunctions.RHTower.PaperCirclePosteriorCalibration
import GaloisForLFunctions.RHTower.PaperCirclePosteriorPrediction

/-! # Calibration debt controls every native character predictor

The source reference budget controls total variation and every posterior character
mean. Consequently it pays for the excess risk of using a different actual
history's optimal predictor. Zero debt is exactly pointwise equality of all next
posteriors, since every observation has positive mass.
-/

open scoped BigOperators NNReal Classical ComplexConjugate
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

private lemma tv_zero_iff {α : Type} [Fintype α] (P Q : Law α) : P.tv Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have hs : ∑ x, |P x-Q x| = 0 := by unfold Law.tv at h; linarith
    apply Law.ext
    intro x
    exact sub_eq_zero.mp (abs_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => abs_nonneg (P x-Q x))).mp hs x
        (Finset.mem_univ x)))
  · rintro rfl
    simp only [Law.tv, sub_self, abs_zero, Finset.sum_const_zero, zero_div]

private lemma character_tv {M : ℕ} (P Q : Law (Grid M)) (u : Grid M) :
    ‖P.Cx (chi u) - Q.Cx (chi u)‖ ≤ 2 * P.tv Q := by
  have he : P.Cx (chi u)-Q.Cx (chi u) = ∑ x, ((P x-Q x : ℝ) : ℂ)*chi u x := by
    simp only [Law.Cx, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_chi, mul_one, Complex.norm_real, Real.norm_eq_abs]
  unfold Law.tv
  linarith

/-- Every frequency shares the same actual reference-debt bound. -/
theorem paperCirclePosteriorCalibration_character_error (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (u : Grid (l+r+10)) :
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (fun z => ‖paperCircleNextCharacterMean a l r k i s t u z -
        paperCircleNextCharacterMean a l r k i v τ u z‖^2) ≤
      4 * paperCirclePosteriorCalibration a l r k i s v t τ := by
  rw [paperCirclePosteriorCalibration_kl, ← Law.Ex_lmul]
  apply Law.Ex_mono
  intro z
  have ht := character_tv (paperCircleNextPosterior a l r k i s t z)
    (paperCircleNextPosterior a l r k i v τ z) u
  have hs := mul_self_le_mul_self (norm_nonneg _) ht
  have hk := Law.tv_sq_le_kl (paperCircleNextPosterior_dominated a l r k i s v t τ z)
  change ‖(paperCircleNextPosterior a l r k i s t z).Cx (chi u) -
    (paperCircleNextPosterior a l r k i v τ z).Cx (chi u)‖^2 ≤ _
  nlinarith

/-- Using another native history's optimum has excess risk at most four times calibration debt. -/
theorem paperCirclePosteriorCalibration_prediction_risk (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleCharacterRisk a l r k i s t u
      (fun z => conj (paperCircleNextCharacterMean a l r k i v τ u z)) ≤
      1 - paperCircleCaptureEnergy a l r k i s t u +
        4 * paperCirclePosteriorCalibration a l r k i s v t τ := by
  rw [paperCircleCharacterRisk_decomposition]
  simp only [← map_sub, Complex.norm_conj]
  simp only [norm_sub_rev (paperCircleNextCharacterMean a l r k i v τ u _)]
  exact add_le_add le_rfl (paperCirclePosteriorCalibration_character_error a l r k i s v t τ u)

/-- Calibration vanishes precisely when every actual conditional posterior agrees. -/
theorem paperCirclePosteriorCalibration_eq_zero_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) :
    paperCirclePosteriorCalibration a l r k i s v t τ = 0 ↔
      ∀ z, paperCircleNextPosterior a l r k i s t z = paperCircleNextPosterior a l r k i v τ z := by
  constructor
  · intro he z
    have hsum : (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => ((paperCircleNextPosterior a l r k i s t z).tv
          (paperCircleNextPosterior a l r k i v τ z))^2) = 0 := by
      apply le_antisymm
      · exact (paperCirclePosteriorCalibration_tv_sq a l r k i s v t τ).trans_eq he
      · exact Law.Ex_nonneg _ (fun z => sq_nonneg _)
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ =>
      mul_nonneg ((paperCircleNextObservationLaw a l r k i s t).nonneg z)
        (sq_nonneg ((paperCircleNextPosterior a l r k i s t z).tv
          (paperCircleNextPosterior a l r k i v τ z))))).mp hsum
    have hz := (mul_eq_zero.mp (ht z (Finset.mem_univ z))).resolve_left
      (paperCircleNextObservationLaw_pos a l r k i s t z).ne'
    exact (tv_zero_iff _ _).mp (sq_eq_zero_iff.mp hz)
  · intro h
    rw [paperCirclePosteriorCalibration_kl]
    simp only [h, Law.kl, Law.entropy, sub_self, Law.Ex_const]

end
end RHTower
