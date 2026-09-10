import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFisherRatioDecoder

/-! # Sequential Fisher identification in actual Gibbs collision histories -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Advancing the observation offset transports the slow source mass by its exact decay rate. -/
theorem egbFixedChargeAGibbsCollisionSlowSourceMass_offset (n m j : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + j) β E : ℝ) =
      (4 / 9 : ℝ) ^ j * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
  change (4 / 9 : ℝ) ^ (m + j + 1) * _ = (4 / 9 : ℝ) ^ j * ((4 / 9 : ℝ) ^ (m + 1) * _)
  rw [show m + j + 1 = j + (m + 1) by omega, pow_add]
  ring

/-- The same time shift transports the fast source mass by the second thermal decay rate. -/
theorem egbFixedChargeAGibbsCollisionFastSourceMass_offset (n m j : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionFastSourceMass n (m + j) β E : ℝ) =
      (1 / 36 : ℝ) ^ j * (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) := by
  change (1 / 36 : ℝ) ^ (m + j + 1) * _ = (1 / 36 : ℝ) ^ j * ((1 / 36 : ℝ) ^ (m + 1) * _)
  rw [show m + j + 1 = j + (m + 1) by omega, pow_add]
  ring

private theorem rate_ratio (j : ℕ) (t : ℝ) :
    (4 / 9 : ℝ) ^ j * (t / (4 : ℝ) ^ j) ^ 2 = (1 / 36 : ℝ) ^ j * t ^ 2 := by
  have hp : ((4 : ℝ) ^ j) ^ 2 = (16 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  have hprod : (1 / 36 : ℝ) ^ j * (16 : ℝ) ^ j = (4 / 9 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  rw [div_pow t ((4 : ℝ) ^ j) 2, hp, ← hprod]
  have hne : (16 : ℝ) ^ j ≠ 0 := by positivity
  field_simp

/-- The actual observed fast-to-slow mass ratio follows the exact geometric chart orbit. -/
theorem egbFixedChargeAGibbsTunable_source_mass_ratio_offset (n k m j : ℕ) (t : ℝ) :
    (egbFixedChargeAGibbsCollisionFastSourceMass n (m + j) 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) =
      (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + j) 1
        (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) * (t / (4 : ℝ) ^ j) ^ 2 := by
  rw [egbFixedChargeAGibbsCollisionFastSourceMass_offset,
    egbFixedChargeAGibbsCollisionSlowSourceMass_offset, egbFixedChargeAGibbsTunable_source_mass_ratio]
  calc
    _ = (egbFixedChargeAGibbsCollisionSlowSourceMass n m 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) * ((1 / 36 : ℝ) ^ j * t ^ 2) := by ring
    _ = _ := by rw [← rate_ratio]; ring

/-- One fixed actual Gibbs energy realizes the entire geometric Fisher history, without retuning at each step. -/
theorem egbFixedChargeAGibbsTunable_fisher_history (n k m j : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n (m + j) 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableFisherCurve (t / (4 : ℝ) ^ j) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass,
    egbFixedChargeAGibbsTunable_source_mass_ratio_offset]
  have hx : 0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + j) 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) := by
    rw [egbFixedChargeAGibbsCollisionSlowSourceMass_offset]
    exact mul_pos (pow_pos (by norm_num) _) (egbFixedChargeAGibbsTunable_slow_mass_pos n k m t)
  generalize (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + j) 1
    (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) = x at hx ⊢
  generalize t / (4 : ℝ) ^ j = z
  have hd : 1 + z ^ 2 ≠ 0 := (show 0 < 1 + z ^ 2 by positivity).ne'
  have hs : x + x * z ^ 2 ≠ 0 := (show 0 < x + x * z ^ 2 by positivity).ne'
  unfold egbFixedChargeAGibbsCollisionFisherShape egbFixedChargeAGibbsTunableFisherCurve
  field_simp
  <;> ring

/-- Two successive actual Gibbs observations identify the source ratio across any grids and attenuations. -/
theorem egbFixedChargeAGibbsTunable_fisher_pair_eq_iff (n k m p q o : ℕ) (t u : ℝ) :
    (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
        egbFixedChargeAGibbsCollisionFisherValue p o 1 (egbFixedChargeAGibbsTunableEnergy p q o u) ∧
      egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
        egbFixedChargeAGibbsCollisionFisherValue p (o + 1) 1 (egbFixedChargeAGibbsTunableEnergy p q o u)) ↔
      t ^ 2 = u ^ 2 := by
  rw [egbFixedChargeAGibbsTunable_fisher_formula, egbFixedChargeAGibbsTunable_fisher_formula,
    egbFixedChargeAGibbsTunable_fisher_history, egbFixedChargeAGibbsTunable_fisher_history]
  simpa only [pow_one] using egbFixedChargeAGibbsTunableFisherCurve_pair_eq_iff t u

/-- The explicit two-reading decoder recovers the ratio from actual Gibbs observations at the chosen offset. -/
theorem egbFixedChargeAGibbsTunable_fisher_ratio_decode (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsFisherRatioDecoder
      (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t))
      (egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t)) =
      t ^ 2 := by
  rw [egbFixedChargeAGibbsTunable_fisher_formula, egbFixedChargeAGibbsTunable_fisher_history]
  simpa only [pow_one] using egbFixedChargeAGibbsFisherRatioDecoder_exact t

end
end GaloisForLFunctions.HTGeometry
