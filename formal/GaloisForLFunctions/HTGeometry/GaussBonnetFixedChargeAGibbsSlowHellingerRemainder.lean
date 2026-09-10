import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowHellingerTaylor

/-!
# Quantitative Hellinger expansion along the positive slow Gibbs family

The square-root rationalization remainder, summed over the critical thermal
kernel from arXiv:2609.00025, identifies collision excess as the leading term.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Squared Hellinger distance has a cubic remainder in the displacement coordinates. -/
theorem egbFixedChargeAGibbsSlow_hellinger_cubic_remainder (n m : ℕ) :
    |finitePacketHellinger
        (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 -
      ((2 : ℝ) ^ (n + 3) / 4) *
        egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)| ≤
      (∑ i : Fin (2 ^ (n + 3)), |egbFixedChargeAGibbsSlowDisplacement n m i| ^ 3) /
        (2 : ℝ) ^ (n + 3) := by
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  have he :
      finitePacketHellinger
          (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
          (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 -
        ((2 : ℝ) ^ (n + 3) / 4) *
          egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
      (∑ i : Fin (2 ^ (n + 3)),
        ((Real.sqrt (1 + egbFixedChargeAGibbsSlowDisplacement n m i) - 1) ^ 2 -
          egbFixedChargeAGibbsSlowDisplacement n m i ^ 2 / 4)) /
        (2 : ℝ) ^ (n + 3) := by
    rw [egbFixedChargeAGibbsSlow_hellinger_displacement_formula,
      egbFixedChargeAGibbsSlow_collision_displacement_formula]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hn]
  have hsum := Finset.abs_sum_le_sum_abs
    (fun i : Fin (2 ^ (n + 3)) =>
      (Real.sqrt (1 + egbFixedChargeAGibbsSlowDisplacement n m i) - 1) ^ 2 -
        egbFixedChargeAGibbsSlowDisplacement n m i ^ 2 / 4) Finset.univ
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
    egbFixedChargeAGibbsSlow_hellinger_coordinate_remainder n m i)
  exact div_le_div_of_nonneg_right (hsum.trans hb) hn.le

/-- The remainder relative to collision excess decays at the slow amplitude rate. -/
theorem egbFixedChargeAGibbsSlow_hellinger_quadratic_remainder (n m : ℕ) :
    |finitePacketHellinger
        (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 -
      ((2 : ℝ) ^ (n + 3) / 4) *
        egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)| ≤
      ((2 : ℝ) ^ (n + 3) / 2) * (2 / 3 : ℝ) ^ m *
        egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) := by
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  calc
    _ ≤ (∑ i, |egbFixedChargeAGibbsSlowDisplacement n m i| ^ 3) /
        (2 : ℝ) ^ (n + 3) := egbFixedChargeAGibbsSlow_hellinger_cubic_remainder n m
    _ ≤ (((2 / 3 : ℝ) ^ m / 2) * ∑ i, egbFixedChargeAGibbsSlowDisplacement n m i ^ 2) /
        (2 : ℝ) ^ (n + 3) :=
      div_le_div_of_nonneg_right (egbFixedChargeAGibbsSlow_displacement_cubic_bound n m) hn.le
    _ = _ := by
      rw [egbFixedChargeAGibbsSlow_collision_displacement_formula]
      field_simp

end
end GaloisForLFunctions.HTGeometry
