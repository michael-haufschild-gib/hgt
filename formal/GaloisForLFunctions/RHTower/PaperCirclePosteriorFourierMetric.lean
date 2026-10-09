import GaloisForLFunctions.RHTower.PaperCirclePosteriorFourierIdentification

/-! # Fourier metric and collision probability of actual native posteriors

Parseval identifies the full squared density error with the average squared
character error. Thus the native calibration debt bounds the entire posterior,
without a grid-cardinality factor. Averaging capture energy over all frequencies
also gives the expected posterior collision probability exactly.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

private lemma real_density_parseval {M : ℕ} (f : Grid M → ℝ) :
    ∑ x, (f x)^2 = (Law.uniform (Grid M)).Ex
      (fun u => ‖∑ x, (f x : ℂ) * chi u x‖^2) := by
  have hf (u : Grid M) : fc (fun x => (f x : ℂ)) u =
      (Period.side M : ℂ) * ∑ x, (f x : ℂ) * chi (-u) x := by
    simp only [fc, expU, Complex.real_smul]
  have h := fc_parseval (fun x => (f x : ℂ))
  simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Period.side_pos M), mul_pow, expU, smul_eq_mul, sq_abs,
    ← Finset.mul_sum] at h
  have he : ∑ x, (f x)^2 = expU (fun u => ‖∑ x, (f x : ℂ) * chi (-u) x‖^2) := by
    change ∑ x, (f x)^2 = Period.side M * ∑ u, ‖∑ x, (f x : ℂ) * chi (-u) x‖^2
    nlinarith only [h, Period.side_pos M]
  rw [expU_reflect (fun u => ‖∑ x, (f x : ℂ) * chi u x‖^2), expU_ex] at he
  exact he

/-- Full density error is the uniform mean of all squared character discrepancies. -/
theorem paperCircleNextPosterior_parseval (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10)))
    (t τ : ℝ≥0) (z : Grid (l+r+10)) :
    (∑ x, (paperCircleNextPosterior a l r k i s t z x -
      paperCircleNextPosterior a l r k i v τ z x)^2) =
      (Law.uniform (Grid (l+r+10))).Ex
        (fun u => ‖paperCircleNextCharacterMean a l r k i s t u z -
          paperCircleNextCharacterMean a l r k i v τ u z‖^2) := by
  simpa only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    paperCircleNextCharacterMean, Law.Cx] using
    real_density_parseval (fun x => paperCircleNextPosterior a l r k i s t z x -
      paperCircleNextPosterior a l r k i v τ z x)

/-- Calibration controls total squared posterior-density error with no dimension factor. -/
theorem paperCirclePosteriorCalibration_density_error (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s v : List (ℝ≥0 × Grid (l+r+10))) (t τ : ℝ≥0) :
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (fun z => ∑ x, (paperCircleNextPosterior a l r k i s t z x -
        paperCircleNextPosterior a l r k i v τ z x)^2) ≤
      4 * paperCirclePosteriorCalibration a l r k i s v t τ := by
  simp_rw [paperCircleNextPosterior_parseval]
  rw [Law.Ex_swap]
  exact (Law.Ex_mono _ (fun u =>
    paperCirclePosteriorCalibration_character_error a l r k i s v t τ u)).trans_eq
      (Law.Ex_const _ _)

/-- Posterior collision probability is the mean squared Fourier character mean. -/
theorem paperCircleNextPosterior_collision_fourier (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z : Grid (l+r+10)) :
    (∑ x, (paperCircleNextPosterior a l r k i s t z x)^2) =
      (Law.uniform (Grid (l+r+10))).Ex
        (fun u => ‖paperCircleNextCharacterMean a l r k i s t u z‖^2) :=
  real_density_parseval (paperCircleNextPosterior a l r k i s t z)

/-- The complete capture-energy spectrum averages to expected posterior collision probability. -/
theorem paperCircleCaptureEnergy_spectral_average (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    (Law.uniform (Grid (l+r+10))).Ex (paperCircleCaptureEnergy a l r k i s t) =
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => ∑ x, (paperCircleNextPosterior a l r k i s t z x)^2) := by
  change (Law.uniform (Grid (l+r+10))).Ex (fun u => paperCircleCaptureEnergy a l r k i s t u) = _
  simp_rw [paperCircleCaptureEnergy_mean_square, paperCircleNextPosterior_collision_fourier]
  exact Law.Ex_swap _ _ _

end
end RHTower
