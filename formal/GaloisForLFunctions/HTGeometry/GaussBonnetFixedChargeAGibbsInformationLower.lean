import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSharpCollision

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem square_root_difference_lower (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (x - y) ^ (2 : ℕ) ≤ 4 * (Real.sqrt x - Real.sqrt y) ^ (2 : ℕ) := by
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hxp := Real.sqrt_nonneg x
  have hyp := Real.sqrt_nonneg y
  have hxle : Real.sqrt x ≤ 1 := by nlinarith
  have hyle : Real.sqrt y ≤ 1 := by nlinarith
  have hsum : (Real.sqrt x + Real.sqrt y) ^ (2 : ℕ) ≤ 4 := by nlinarith
  calc
    (x - y) ^ (2 : ℕ) = ((Real.sqrt x) ^ (2 : ℕ) - (Real.sqrt y) ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [hxs, hys]
    _ = (Real.sqrt x - Real.sqrt y) ^ (2 : ℕ) * (Real.sqrt x + Real.sqrt y) ^ (2 : ℕ) := by ring
    _ ≤ (Real.sqrt x - Real.sqrt y) ^ (2 : ℕ) * 4 :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

/-- Normalization bounds each Gibbs population coordinate by one. -/
theorem egbFixedChargeAGibbsPopulation_le_one (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    egbFixedChargeAGibbsMarkovPopulation n m β E i ≤ 1 := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E j) (Finset.mem_univ i)
  rw [egbFixedChargeAGibbsMarkovPopulation_mass] at h
  exact h

/-- Squared Hellinger distinguishability bounds collision excess from below. -/
theorem egbFixedChargeAGibbsCollisionExcess_hellinger_lower (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E ≤
      4 * finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) := by
  have hu0 : 0 ≤ ((2 : ℝ) ^ (n + 3))⁻¹ := by positivity
  have hu1 : ((2 : ℝ) ^ (n + 3))⁻¹ ≤ 1 := by
    have hn : 1 ≤ (2 : ℝ) ^ (n + 3) := one_le_pow₀ (by norm_num)
    have hpos : 0 < (2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
    have he : ((2 : ℝ) ^ (n + 3))⁻¹ * (2 : ℝ) ^ (n + 3) = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith
  rw [egbFixedChargeAHellinger_coordinate_square, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => square_root_difference_lower _ _
    (egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E i) hu0
    (egbFixedChargeAGibbsPopulation_le_one n m β E i) hu1

/-- Relative entropy is at least one quarter of collision excess for every Gibbs population. -/
theorem egbFixedChargeAGibbsEntropyDeficit_collision_lower (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E / 4 ≤ egbFixedChargeAGibbsEntropyDeficit n m β E := by
  have h := egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m β E
  have hd := egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E
  linarith

end
end GaloisForLFunctions.HTGeometry
