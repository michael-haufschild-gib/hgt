import GaloisForLFunctions.RHTower.PaperCircleObservationHistory

/-! # Aligned observations preserve and strengthen native localization

When all observed positions agree, the posterior is exactly the translated Gibbs law
of the accumulated native energy. Adding another aligned observation increases every
centered cosine expectation and decreases every centered character fluctuation.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem paperCircleHistoryLikelihood_aligned (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (z x : Grid M) :
    paperCircleHistoryLikelihood a M k (ts.map fun t => (t,z)) x =
      Thermal.boltz (Thermal.mixForm
        (paperCircleObservationProfile a M k (ts.map fun t => (t,z)))) (z-x) := by
  induction ts with
  | nil => simp [paperCircleHistoryLikelihood, paperCircleObservationProfile, Thermal.tune,
      Thermal.sumE, Thermal.mixForm, Thermal.boltz, Thermal.form_zero]
  | cons t ts ih =>
    simp only [List.map_cons, paperCircleHistoryLikelihood_cons]
    rw [ih]
    exact (Thermal.boltz_sum _ _ _).symm

theorem paperCircleHistoryEvidence_aligned (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (z : Grid M) :
    paperCircleHistoryEvidence a M k (ts.map fun t => (t,z)) =
      Thermal.q (Thermal.mixForm
        (paperCircleObservationProfile a M k (ts.map fun t => (t,z)))) 0 := by
  rw [paperCircleHistoryEvidence]
  change expU (fun x => paperCircleHistoryLikelihood a M k (ts.map fun t => (t,z)) x) = _
  simp_rw [paperCircleHistoryLikelihood_aligned]
  let B := Thermal.mixForm (paperCircleObservationProfile a M k (ts.map fun t => (t,z)))
  change expU (fun x => Thermal.boltz B (z-x)) = _
  calc
    _ = expU (fun x => Thermal.boltz B (z+x)) := by
      simpa only [sub_eq_add_neg] using expU_reflect (fun x => Thermal.boltz B (z+x))
    _ = expU (Thermal.boltz B) := expU_translate _ z
    _ = _ := (Thermal.q_origin B).symm

/-- Repeated observations at one position produce exactly the summed-energy observation law. -/
theorem paperCircleHistoryPosterior_aligned (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (z : Grid M) :
    paperCircleHistoryPosterior a M k (ts.map fun t => (t,z)) =
      Thermal.channel (Thermal.mixForm
        (paperCircleObservationProfile a M k (ts.map fun t => (t,z)))) z := by
  apply Law.ext
  intro x
  rw [paperCircleHistoryPosterior_apply, paperCircleHistoryEvidence_aligned,
    paperCircleHistoryLikelihood_aligned, Thermal.channel_apply, Thermal.label_apply, Thermal.K]
  have h := Thermal.boltz_even
    (Thermal.mixForm (paperCircleObservationProfile a M k (ts.map fun t => (t,z)))) (z-x)
  rw [neg_sub] at h
  rw [h]
  ring

theorem paperCircleHistoryPosterior_aligned_ex (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (z : Grid M) (f : Grid M → ℝ) :
    (paperCircleHistoryPosterior a M k (ts.map fun t => (t,z))).Ex (fun x => f (x-z)) =
      (Thermal.label (Thermal.mixForm
        (paperCircleObservationProfile a M k (ts.map fun t => (t,z))))).Ex f := by
  rw [paperCircleHistoryPosterior_aligned, Thermal.ch_noise]

/-- Each additional aligned observation strengthens every centered cosine mode. -/
theorem paperCircleHistoryPosterior_aligned_cosine (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (t : ℝ≥0) (z u : Grid M) :
    (paperCircleHistoryPosterior a M k (ts.map fun t => (t,z))).Ex
      (fun x => Thermal.wave u (x-z)) ≤
    (paperCircleHistoryPosterior a M k ((t::ts).map fun t => (t,z))).Ex
      (fun x => Thermal.wave u (x-z)) := by
  rw [paperCircleHistoryPosterior_aligned_ex, paperCircleHistoryPosterior_aligned_ex,
    ← Thermal.cred_ex, ← Thermal.cred_ex]
  apply Thermal.cred_mono
  · exact Thermal.mix_nonneg (paperCircleObservationProfile_nonneg a M k _)
  · exact le_add_of_nonneg_left (paperCircleLocalizedForm_nonneg a M k t)

/-- The same update decreases the mean squared fluctuation of every centered character. -/
theorem paperCircleHistoryPosterior_aligned_phase (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (t : ℝ≥0) (z u : Grid M) :
    (paperCircleHistoryPosterior a M k ((t::ts).map fun t => (t,z))).Ex
      (fun x => ‖1-chi u (x-z)‖^2) ≤
    (paperCircleHistoryPosterior a M k (ts.map fun t => (t,z))).Ex
      (fun x => ‖1-chi u (x-z)‖^2) := by
  have h := paperCircleHistoryPosterior_aligned_cosine a M k ts t z u
  simp_rw [Thermal.norm_phase_sq, Thermal.cost, Law.Ex_lmul, Law.Ex_sub, Law.Ex_const]
  linarith

private theorem aligned_spatial_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (t : ℝ≥0) (z : Grid M) :
    Thermal.S M (paperCircleLocalizationWidth M k) ≤
      Thermal.mixForm (paperCircleObservationProfile a M k ((t::ts).map fun t => (t,z))) :=
  (paperCircleLocalizedForm_spatial_le a M k t).trans
    (le_add_of_nonneg_right (Thermal.mix_nonneg (paperCircleObservationProfile_nonneg a M k _)))

/-- Arbitrarily many aligned observations retain the original spatial concentration bound. -/
theorem paperCircleHistoryPosterior_aligned_variance (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (ts : List ℝ≥0) (t : ℝ≥0) (z : Grid M) :
    (paperCircleHistoryPosterior a M k ((t::ts).map fun t => (t,z))).Ex
      (fun x => (Dyadic.diam (x-z))^2) ≤ 100 / paperCircleLocalizationWidth M k ^ 2 := by
  rw [paperCircleHistoryPosterior_aligned_ex a M k (t::ts) z (fun x => (Dyadic.diam x)^2)]
  exact Thermal.S_variance _ (paperCircleLocalizationWidth_ge_one M k)
    (paperCircleLocalizationWidth_le_grid M k) _ (aligned_spatial_le a M k ts t z)

end
end RHTower
