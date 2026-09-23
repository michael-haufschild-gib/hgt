import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableSpectralEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionFisherStepSigns

/-! # Exact Fisher geometry for every tunable Gibbs state -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The normalized Fisher curve after compensating for the two decay rates. -/
def egbFixedChargeAGibbsTunableFisherCurve (t : ℝ) : ℝ :=
  (25 / 36 : ℝ) * t ^ (2 : ℕ) / (1 + t ^ (2 : ℕ)) ^ (2 : ℕ)

private theorem fisher_shape_square_ratio (x t : ℝ) (hx : 0 < x) :
    egbFixedChargeAGibbsCollisionFisherShape x (x * t ^ (2 : ℕ)) =
      egbFixedChargeAGibbsTunableFisherCurve t := by
  have hd : 1 + t ^ (2 : ℕ) ≠ 0 := (show 0 < 1 + t ^ (2 : ℕ) by positivity).ne'
  have hs : x + x * t ^ (2 : ℕ) ≠ 0 := (show 0 < x + x * t ^ (2 : ℕ) by positivity).ne'
  unfold egbFixedChargeAGibbsCollisionFisherShape egbFixedChargeAGibbsTunableFisherCurve
  field_simp [hx.ne', hd, hs]
  <;> ring

/-- Actual Gibbs states realize the same exact Fisher curve at every grid, attenuation, and chosen time offset. -/
theorem egbFixedChargeAGibbsTunable_fisher_formula (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableFisherCurve t := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass, egbFixedChargeAGibbsTunable_source_mass_ratio]
  exact fisher_shape_square_ratio _ t (egbFixedChargeAGibbsTunable_slow_mass_pos n k m t)

/-- The tunable Fisher curve is continuous across the pure-mode endpoint as well as every mixed state. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_continuous :
    Continuous egbFixedChargeAGibbsTunableFisherCurve := by
  unfold egbFixedChargeAGibbsTunableFisherCurve
  exact (continuous_const.mul (continuous_id.pow 2)).div
    ((continuous_const.add (continuous_id.pow 2)).pow 2) (fun t => by positivity)

/-- The pure slow state has zero Fisher value and the balanced observed mixture attains the universal bound. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_endpoints :
    egbFixedChargeAGibbsTunableFisherCurve 0 = 0 ∧
      egbFixedChargeAGibbsTunableFisherCurve 1 = (25 / 144 : ℝ) := by
  norm_num [egbFixedChargeAGibbsTunableFisherCurve]

/-- Every tunable Fisher value lies inside the exact universal interval. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_bounds (t : ℝ) :
    0 ≤ egbFixedChargeAGibbsTunableFisherCurve t ∧
      egbFixedChargeAGibbsTunableFisherCurve t ≤ (25 / 144 : ℝ) := by
  rw [← egbFixedChargeAGibbsTunable_fisher_formula 0 0 0 t]
  exact ⟨egbFixedChargeAGibbsCollisionFisherValue_nonneg _ _ _ _,
    egbFixedChargeAGibbsCollisionFisherValue_upper_bound _ _ _ _⟩

/-- Every allowed Fisher value is realized by an explicit family of actual positive Gibbs states. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_range :
    Set.range egbFixedChargeAGibbsTunableFisherCurve = Set.Icc 0 (25 / 144 : ℝ) := by
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    exact egbFixedChargeAGibbsTunableFisherCurve_bounds t
  · intro hv
    have h := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      egbFixedChargeAGibbsTunableFisherCurve_continuous.continuousOn
    rw [(egbFixedChargeAGibbsTunableFisherCurve_endpoints).1,
      (egbFixedChargeAGibbsTunableFisherCurve_endpoints).2] at h
    obtain ⟨t, _, ht⟩ := h hv
    exact ⟨t, ht⟩

/-- On every fixed grid and observation offset, genuine Gibbs energies fill the entire universal Fisher interval. -/
theorem egbFixedChargeAGibbs_fisher_exact_range (n m : ℕ) :
    Set.range (fun E : Fin (2 ^ (n + 3)) → ℝ => egbFixedChargeAGibbsCollisionFisherValue n m 1 E) =
      Set.Icc 0 (25 / 144 : ℝ) := by
  ext v
  constructor
  · rintro ⟨E, rfl⟩
    exact ⟨egbFixedChargeAGibbsCollisionFisherValue_nonneg _ _ _ _,
      egbFixedChargeAGibbsCollisionFisherValue_upper_bound _ _ _ _⟩
  · intro hv
    rw [← egbFixedChargeAGibbsTunableFisherCurve_range] at hv
    obtain ⟨t, ht⟩ := hv
    exact ⟨egbFixedChargeAGibbsTunableEnergy n 0 m t,
      (egbFixedChargeAGibbsTunable_fisher_formula n 0 m t).trans ht⟩

end
end GaloisForLFunctions.HTGeometry
