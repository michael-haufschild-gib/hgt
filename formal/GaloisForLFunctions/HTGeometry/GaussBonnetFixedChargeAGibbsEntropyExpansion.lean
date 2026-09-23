import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHellingerExpansion

/-!
# Eventual entropy expansion for arbitrary critical Gibbs inputs

Finite-coordinate convergence puts every Gibbs population in a common Taylor
interval. The corpus logarithm remainder then identifies collision excess as
the leading relative-information observable for the arXiv:2609.00025 kernel.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

private theorem entropy_coordinate_remainder (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |(1 + x) * Real.log (1 + x) - x - x ^ (2 : ℕ) / 2| ≤ 7 * |x| ^ (3 : ℕ) := by
  have hlog := abs_log_one_add_taylor_le (x := x) (by linarith)
  have hlin : |1 + x| ≤ 3 / 2 := by
    have h := abs_add_le (1 : ℝ) x
    norm_num only [abs_one] at h
    linarith
  have he : (1 + x) * Real.log (1 + x) - x - x ^ (2 : ℕ) / 2 =
      (1 + x) * (Real.log (1 + x) - x + x ^ (2 : ℕ) / 2) - x ^ (3 : ℕ) / 2 := by ring
  rw [he]
  have h : |(1 + x) * (Real.log (1 + x) - x + x ^ (2 : ℕ) / 2) - x ^ (3 : ℕ) / 2| ≤
      |(1 + x) * (Real.log (1 + x) - x + x ^ (2 : ℕ) / 2)| + |x ^ (3 : ℕ) / 2| := by
    rw [abs_le]
    constructor <;> linarith [
      neg_abs_le ((1 + x) * (Real.log (1 + x) - x + x ^ (2 : ℕ) / 2)),
      le_abs_self ((1 + x) * (Real.log (1 + x) - x + x ^ (2 : ℕ) / 2)),
      neg_abs_le (x ^ (3 : ℕ) / 2), le_abs_self (x ^ (3 : ℕ) / 2)]
  rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have hp := mul_le_mul hlin hlog (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  nlinarith [pow_nonneg (abs_nonneg x) 3]


/-- Relative information in exact displacement coordinates for every Gibbs landscape. -/
theorem egbFixedChargeAGibbsEntropyDeficit_displacement_formula (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n m β E =
      (∑ i : Fin (2 ^ (n + 3)),
        (1 + egbFixedChargeAGibbsDisplacement n m β E i) *
          Real.log (1 + egbFixedChargeAGibbsDisplacement n m β E i)) / (2 : ℝ) ^ (n + 3) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold egbFixedChargeAGibbsEntropyDeficit relEntropy
  rw [tsum_fintype]
  simp_rw [egbFixedChargeAGibbsDisplacement_population]
  have hr (i : Fin (2 ^ (n + 3))) :
      ((1 + egbFixedChargeAGibbsDisplacement n m β E i) / (2 : ℝ) ^ (n + 3)) /
        ((2 : ℝ) ^ (n + 3))⁻¹ = 1 + egbFixedChargeAGibbsDisplacement n m β E i := by field_simp
  simp_rw [hr]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All Gibbs coordinates eventually satisfy the same explicit cubic entropy remainder. -/
theorem egbFixedChargeAGibbsEntropyDeficit_eventually_coordinate_remainder (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin (2 ^ (n + 3)),
      |(1 + egbFixedChargeAGibbsDisplacement n m β E i) *
          Real.log (1 + egbFixedChargeAGibbsDisplacement n m β E i) -
        egbFixedChargeAGibbsDisplacement n m β E i -
          egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) / 2| ≤
        7 * |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ) := by
  filter_upwards [egbFixedChargeAGibbsDisplacementSize_eventually_half n β E] with m hm
  intro i
  exact entropy_coordinate_remainder _ ((egbFixedChargeAGibbsDisplacementSize_coordinate n m β E i).trans hm)

/-- The total entropy error is eventually bounded by the complete cubic displacement mass. -/
theorem egbFixedChargeAGibbsEntropyDeficit_eventually_cubic_remainder (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∀ᶠ m : ℕ in atTop,
      |egbFixedChargeAGibbsEntropyDeficit n m β E -
        ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n m β E| ≤
          (7 / (2 : ℝ) ^ (n + 3)) * ∑ i, |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ) := by
  filter_upwards [egbFixedChargeAGibbsEntropyDeficit_eventually_coordinate_remainder n β E] with m hm
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  have he : egbFixedChargeAGibbsEntropyDeficit n m β E -
        ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n m β E =
      (∑ i : Fin (2 ^ (n + 3)),
        ((1 + egbFixedChargeAGibbsDisplacement n m β E i) *
            Real.log (1 + egbFixedChargeAGibbsDisplacement n m β E i) -
          egbFixedChargeAGibbsDisplacement n m β E i -
            egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) / 2)) / (2 : ℝ) ^ (n + 3) := by
    rw [egbFixedChargeAGibbsEntropyDeficit_displacement_formula,
      egbFixedChargeAGibbsDisplacement_collision_formula]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div,
      egbFixedChargeAGibbsDisplacement_mass_zero, sub_zero]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hn]
  have hs := Finset.abs_sum_le_sum_abs
    (fun i : Fin (2 ^ (n + 3)) =>
      (1 + egbFixedChargeAGibbsDisplacement n m β E i) *
          Real.log (1 + egbFixedChargeAGibbsDisplacement n m β E i) -
        egbFixedChargeAGibbsDisplacement n m β E i -
          egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) / 2) Finset.univ
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) => hm i)
  have h := div_le_div_of_nonneg_right (hs.trans hb) hn.le
  rw [← Finset.mul_sum] at h
  calc
    _ ≤ (7 * ∑ i, |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ)) / (2 : ℝ) ^ (n + 3) := h
    _ = _ := by ring

/-- Relative entropy eventually differs from half the normalized collision excess by a vanishing relative error. -/
theorem egbFixedChargeAGibbsEntropyDeficit_eventually_quadratic_remainder (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∀ᶠ m : ℕ in atTop,
      |egbFixedChargeAGibbsEntropyDeficit n m β E -
        ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n m β E| ≤
        (7 * (2 : ℝ) ^ (n + 3)) * egbFixedChargeAGibbsDisplacementSize n m β E *
          egbFixedChargeAGibbsCollisionExcess n m β E := by
  filter_upwards [egbFixedChargeAGibbsEntropyDeficit_eventually_cubic_remainder n β E] with m hm
  have hn : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  calc
    _ ≤ (7 / (2 : ℝ) ^ (n + 3)) * ∑ i, |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ) := hm
    _ ≤ (7 / (2 : ℝ) ^ (n + 3)) *
        (egbFixedChargeAGibbsDisplacementSize n m β E *
          ∑ i, egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left (egbFixedChargeAGibbsDisplacementSize_cubic_bound n m β E) (by positivity)
    _ = _ := by
      rw [egbFixedChargeAGibbsDisplacement_collision_formula]
      field_simp
      <;> ring

end
end GaloisForLFunctions.HTGeometry
