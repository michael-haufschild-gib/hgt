import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeFisherHistory

/-! # Actual pure Gibbs sources invisible to Fisher history and total mass
The obstruction retains a positive survivor: two source moments reconstruct both
masses, and the first moment distinguishes the two normalized pure endpoints. -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- Both pure source rays occur as actual full-support Gibbs states with identically zero Fisher histories. -/
theorem egbFixedChargeAGibbsCone_pure_histories_zero (n k m : ℕ) :
    (∀ l : ℕ, egbFixedChargeAGibbsCollisionFisherValue n l 1 (egbFixedChargeAGibbsConeEnergy n k m 1 0) = 0) ∧
      (∀ l : ℕ, egbFixedChargeAGibbsCollisionFisherValue n l 1 (egbFixedChargeAGibbsConeEnergy n k m 0 1) = 0) := by
  exact ⟨(egbFixedChargeAGibbsCone_fisher_history_zero_iff n k m 1 0).2 (Or.inr rfl),
    (egbFixedChargeAGibbsCone_fisher_history_zero_iff n k m 0 1).2 (Or.inl rfl)⟩

/-- The indistinguishable pure histories have genuinely different actual positive source measures. -/
theorem egbFixedChargeAGibbsCone_pure_actual_sources_ne (n k m : ℕ) :
    egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsConeEnergy n k m 1 0) ≠
      egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsConeEnergy n k m 0 1) := by
  intro h
  rw [egbFixedChargeAGibbsCone_source_factorization, egbFixedChargeAGibbsCone_source_factorization,
    ← egbFixedChargeAGibbsConeSource_scale, ← egbFixedChargeAGibbsConeSource_scale] at h
  simp only [mul_one, mul_zero, egbFixedChargeAGibbsConeSource_eq_iff] at h
  have hp := egbFixedChargeAGibbsConeScale_pos n k m 1 0
  rw [h.1] at hp
  norm_num at hp

/-- Normalized pure sources have the same total mass but distinct exact first moments. -/
theorem egbFixedChargeAGibbsCone_pure_moments :
    hausdorffMoment (egbFixedChargeAGibbsConeSource 1 0) 0 = 1 ∧
      hausdorffMoment (egbFixedChargeAGibbsConeSource 0 1) 0 = 1 ∧
      hausdorffMoment (egbFixedChargeAGibbsConeSource 1 0) 1 = (4 / 9 : ℝ) ∧
      hausdorffMoment (egbFixedChargeAGibbsConeSource 0 1) 1 = (1 / 36 : ℝ) := by
  norm_num [egbFixedChargeAGibbsConeSource_moment]

/-- Even the entire actual Fisher history plus normalized total source mass admits no universal source decoder. -/
theorem egbFixedChargeAGibbsCone_no_history_mass_source_decoder (n k m : ℕ) :
    ¬ ∃ h : (ℕ → ℝ) → ℝ → Measure HausdorffSourceSpace, ∀ x y : NNReal,
      h (fun l => egbFixedChargeAGibbsCollisionFisherValue n l 1 (egbFixedChargeAGibbsConeEnergy n k m x y))
        (hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 0) = egbFixedChargeAGibbsConeSource x y := by
  rintro ⟨h, hh⟩
  have hs := hh 1 0
  have hf := hh 0 1
  have hslow : (fun l => egbFixedChargeAGibbsCollisionFisherValue n l 1
      (egbFixedChargeAGibbsConeEnergy n k m 1 0)) = (fun _ : ℕ => (0 : ℝ)) :=
    funext (egbFixedChargeAGibbsCone_pure_histories_zero n k m).1
  have hfast : (fun l => egbFixedChargeAGibbsCollisionFisherValue n l 1
      (egbFixedChargeAGibbsConeEnergy n k m 0 1)) = (fun _ : ℕ => (0 : ℝ)) :=
    funext (egbFixedChargeAGibbsCone_pure_histories_zero n k m).2
  rw [hslow, egbFixedChargeAGibbsCone_pure_moments.1] at hs
  rw [hfast, egbFixedChargeAGibbsCone_pure_moments.2.1] at hf
  have he := (egbFixedChargeAGibbsConeSource_eq_iff 1 0 0 1).1 (hs.symm.trans hf)
  norm_num at he

/-- The positive survivor is exact two-moment recovery of both masses on the whole cone, with neither pure endpoint excluded. -/
theorem egbFixedChargeAGibbsConeSource_masses_from_moments (x y : NNReal) :
    (x : ℝ) = (12 / 5 : ℝ) * (hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 1 -
      (1 / 36 : ℝ) * hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 0) ∧
    (y : ℝ) = (12 / 5 : ℝ) * ((4 / 9 : ℝ) * hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 0 -
      hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 1) := by
  simp only [egbFixedChargeAGibbsConeSource_moment, pow_zero, pow_one, mul_one]
  constructor <;> ring

end
end GaloisForLFunctions.HTGeometry
