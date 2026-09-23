import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsDisplacementSize

/-!
# Global Hellinger expansion for every Gibbs population

Square-root rationalization and the common displacement bound give a global
quadratic approximation for all Gibbs inputs of the critical thermal kernel
extracted from arXiv:2609.00025.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Squared Hellinger distance of an arbitrary evolved Gibbs law from uniformity. -/
def egbFixedChargeAGibbsHellingerSquared (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
    (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ)

private theorem sqrt_distance_cubic_remainder (x : ℝ) (hx : 0 ≤ 1 + x) :
    |(Real.sqrt (1 + x) - 1) ^ (2 : ℕ) - x ^ (2 : ℕ) / 4| ≤ |x| ^ (3 : ℕ) := by
  set s := Real.sqrt (1 + x)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ (2 : ℕ) = 1 + x := Real.sq_sqrt hx
  have hx' : x = (s - 1) * (s + 1) := by nlinarith
  have he : (s - 1) ^ (2 : ℕ) - x ^ (2 : ℕ) / 4 = -((s - 1) ^ (3 : ℕ) * (s + 3) / 4) := by
    rw [hx']
    ring
  change |(s - 1) ^ (2 : ℕ) - x ^ (2 : ℕ) / 4| ≤ |x| ^ (3 : ℕ)
  rw [he, abs_neg, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (by linarith : 0 ≤ s + 3), abs_of_pos (by norm_num : (0 : ℝ) < 4),
    hx', abs_mul, abs_of_nonneg (by linarith : 0 ≤ s + 1), mul_pow]
  have hc : (s + 3) / 4 ≤ (s + 1) ^ (3 : ℕ) := by
    nlinarith [pow_nonneg hs 3, sq_nonneg s]
  calc
    _ = |s - 1| ^ (3 : ℕ) * ((s + 3) / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (pow_nonneg (abs_nonneg _) 3)


/-- Every Gibbs coordinate has a global cubic square-root remainder. -/
theorem egbFixedChargeAGibbsHellingerSquared_coordinate_remainder (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    |(Real.sqrt (1 + egbFixedChargeAGibbsDisplacement n m β E i) - 1) ^ (2 : ℕ) -
        egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) / 4| ≤
      |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ) := by
  apply sqrt_distance_cubic_remainder
  linarith [egbFixedChargeAGibbsDisplacement_above_neg_one n m β E i]

/-- The exact Hellinger square in the general displacement coordinates. -/
theorem egbFixedChargeAGibbsHellingerSquared_displacement_formula (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsHellingerSquared n m β E =
      (∑ i : Fin (2 ^ (n + 3)),
        (Real.sqrt (1 + egbFixedChargeAGibbsDisplacement n m β E i) - 1) ^ (2 : ℕ)) /
          (2 : ℝ) ^ (n + 3) := by
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  have hs : Real.sqrt ((2 : ℝ) ^ (n + 3)) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  unfold egbFixedChargeAGibbsHellingerSquared
  rw [egbFixedChargeAHellinger_coordinate_square, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [egbFixedChargeAGibbsDisplacement_population, Real.sqrt_div' _ hn.le, Real.sqrt_inv]
  calc
    _ = ((Real.sqrt (1 + egbFixedChargeAGibbsDisplacement n m β E i) - 1) /
        Real.sqrt ((2 : ℝ) ^ (n + 3))) ^ (2 : ℕ) := by field_simp <;> ring
    _ = _ := by rw [div_pow, Real.sq_sqrt hn.le]

/-- Summed square-root errors are bounded by the complete cubic displacement mass. -/
theorem egbFixedChargeAGibbsHellingerSquared_cubic_remainder (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    |egbFixedChargeAGibbsHellingerSquared n m β E -
      ((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsCollisionExcess n m β E| ≤
      (∑ i, |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ)) / (2 : ℝ) ^ (n + 3) := by
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  have he : egbFixedChargeAGibbsHellingerSquared n m β E -
        ((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsCollisionExcess n m β E =
      (∑ i : Fin (2 ^ (n + 3)),
        ((Real.sqrt (1 + egbFixedChargeAGibbsDisplacement n m β E i) - 1) ^ (2 : ℕ) -
          egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) / 4)) / (2 : ℝ) ^ (n + 3) := by
    rw [egbFixedChargeAGibbsHellingerSquared_displacement_formula,
      egbFixedChargeAGibbsDisplacement_collision_formula]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hn]
  have hs := Finset.abs_sum_le_sum_abs
    (fun i : Fin (2 ^ (n + 3)) =>
      (Real.sqrt (1 + egbFixedChargeAGibbsDisplacement n m β E i) - 1) ^ (2 : ℕ) -
        egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) / 4) Finset.univ
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
    egbFixedChargeAGibbsHellingerSquared_coordinate_remainder n m β E i)
  exact div_le_div_of_nonneg_right (hs.trans hb) hn.le

/-- The error relative to collision excess is controlled by the vanishing common displacement bound. -/
theorem egbFixedChargeAGibbsHellingerSquared_quadratic_remainder (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    |egbFixedChargeAGibbsHellingerSquared n m β E -
      ((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsCollisionExcess n m β E| ≤
      (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsDisplacementSize n m β E *
        egbFixedChargeAGibbsCollisionExcess n m β E := by
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  calc
    _ ≤ (∑ i, |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ)) / (2 : ℝ) ^ (n + 3) :=
      egbFixedChargeAGibbsHellingerSquared_cubic_remainder n m β E
    _ ≤ (egbFixedChargeAGibbsDisplacementSize n m β E *
        ∑ i, egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ)) / (2 : ℝ) ^ (n + 3) :=
      div_le_div_of_nonneg_right (egbFixedChargeAGibbsDisplacementSize_cubic_bound n m β E) hn.le
    _ = _ := by
      rw [egbFixedChargeAGibbsDisplacement_collision_formula]
      field_simp

end
end GaloisForLFunctions.HTGeometry
