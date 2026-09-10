import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHausdorffSource

/-!
# Exact complete-monotonicity hierarchy of collision histories

Every signed finite difference is another positive mixture of the same two
rates. The order of the difference changes its weights but not its spectral
support. Strictness at every order detects activity, including pure modes.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Signed iterated forward difference of a shifted collision sequence. -/
def egbFixedChargeAGibbsCollisionSignedDifference (n o m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  (-1 : ℝ) ^ k * ((fwdDiff 1)^[k]
    (fun j : ℕ => egbFixedChargeAGibbsCollisionExcess n (j + o + 1) β E) m)

private theorem collision_geometric (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E) =
      (fun m : ℕ => ∑ i : Fin 2,
        (![(4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E,
          (1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E] i) *
        (![(4 / 9 : ℝ), (1 / 36 : ℝ)] i) ^ m) := by
  funext m
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + o) β E]
  have he : m + o + 1 = (o + 1) + m := by omega
  rw [he, pow_add (4 / 9 : ℝ) (o + 1) m, pow_add (1 / 36 : ℝ) (o + 1) m]
  ring

/-- Every signed difference has an exact positive two-rate decomposition. -/
theorem egbFixedChargeAGibbsCollisionSignedDifference_formula (n o m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionSignedDifference n o m k β E =
      (5 / 9 : ℝ) ^ k * (4 / 9 : ℝ) ^ (m + o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (35 / 36 : ℝ) ^ k * (1 / 36 : ℝ) ^ (m + o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [egbFixedChargeAGibbsCollisionSignedDifference, collision_geometric,
    fwdDiff_iter_geometricCombination, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hr : (-1 : ℝ) ^ k * ((4 / 9 : ℝ) - 1) ^ k = (5 / 9 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  have hs : (-1 : ℝ) ^ k * ((1 / 36 : ℝ) - 1) ^ k = (35 / 36 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  have he : m + o + 1 = (o + 1) + m := by omega
  rw [he, pow_add (4 / 9 : ℝ) (o + 1) m, pow_add (1 / 36 : ℝ) (o + 1) m]
  calc
    _ = ((-1 : ℝ) ^ k * ((4 / 9 : ℝ) - 1) ^ k) * (4 / 9 : ℝ) ^ (o + 1) *
          (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsSlowModeEnergy n β E +
        ((-1 : ℝ) ^ k * ((1 / 36 : ℝ) - 1) ^ k) * (1 / 36 : ℝ) ^ (o + 1) *
          (1 / 36 : ℝ) ^ m * egbFixedChargeAGibbsFastModeEnergy n β E := by ring
    _ = _ := by rw [hr, hs]; ring

/-- All signed finite differences are nonnegative, at every order and offset. -/
theorem egbFixedChargeAGibbsCollisionSignedDifference_nonneg (n o m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 ≤ egbFixedChargeAGibbsCollisionSignedDifference n o m k β E := by
  exact egbFixedChargeAGibbsCollisionExcess_hausdorff_completelyMonotone n o β E m k

/-- A signed difference vanishes precisely when both collision sectors are absent. -/
theorem egbFixedChargeAGibbsCollisionSignedDifference_zero_iff (n o m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionSignedDifference n o m k β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [egbFixedChargeAGibbsCollisionSignedDifference_formula]
  have hr : 0 < (5 / 9 : ℝ) ^ k * (4 / 9 : ℝ) ^ (m + o + 1) := by positivity
  have hs : 0 < (35 / 36 : ℝ) ^ k * (1 / 36 : ℝ) ^ (m + o + 1) := by positivity
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  have hAr := mul_nonneg hr.le hA
  have hBs := mul_nonneg hs.le hB
  constructor
  · intro h
    have h1 : (5 / 9 : ℝ) ^ k * (4 / 9 : ℝ) ^ (m + o + 1) *
        egbFixedChargeAGibbsSlowModeEnergy n β E = 0 := by linarith
    have h2 : (35 / 36 : ℝ) ^ k * (1 / 36 : ℝ) ^ (m + o + 1) *
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by linarith
    exact ⟨(mul_eq_zero.mp h1).resolve_left hr.ne', (mul_eq_zero.mp h2).resolve_left hs.ne'⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    ring

/-- Every difference order is strictly positive exactly for active collision histories. -/
theorem egbFixedChargeAGibbsCollisionSignedDifference_pos_iff (n o m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsCollisionSignedDifference n o m k β E ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∨
        0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  constructor
  · intro hp
    by_contra hn
    push_neg at hn
    have hz := (egbFixedChargeAGibbsCollisionSignedDifference_zero_iff n o m k β E).mpr
      ⟨le_antisymm hn.1 hA, le_antisymm hn.2 hB⟩
    linarith
  · intro hp
    rw [egbFixedChargeAGibbsCollisionSignedDifference_formula]
    rcases hp with ha | hb <;> positivity

/-- Passing to the next difference order measures the loss of the current signed difference. -/
theorem egbFixedChargeAGibbsCollisionSignedDifference_next_order (n o m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionSignedDifference n o m (k + 1) β E =
      egbFixedChargeAGibbsCollisionSignedDifference n o m k β E -
        egbFixedChargeAGibbsCollisionSignedDifference n o (m + 1) k β E := by
  rw [egbFixedChargeAGibbsCollisionSignedDifference_formula,
    egbFixedChargeAGibbsCollisionSignedDifference_formula,
    egbFixedChargeAGibbsCollisionSignedDifference_formula]
  have he : m + 1 + o + 1 = (m + o + 1) + 1 := by omega
  rw [he, pow_succ (5 / 9 : ℝ) k, pow_succ (35 / 36 : ℝ) k,
    pow_succ (4 / 9 : ℝ) (m + o + 1), pow_succ (1 / 36 : ℝ) (m + o + 1)]
  ring

/-- Every signed difference hierarchy decreases strictly in time exactly for active histories. -/
theorem egbFixedChargeAGibbsCollisionSignedDifference_strictAnti_iff (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    StrictAnti (fun m : ℕ => egbFixedChargeAGibbsCollisionSignedDifference n o m k β E) ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∨
        0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  constructor
  · intro h
    have hs := h (show (0 : ℕ) < 1 by omega)
    change egbFixedChargeAGibbsCollisionSignedDifference n o 1 k β E <
      egbFixedChargeAGibbsCollisionSignedDifference n o 0 k β E at hs
    have hn := egbFixedChargeAGibbsCollisionSignedDifference_nonneg n o 1 k β E
    exact (egbFixedChargeAGibbsCollisionSignedDifference_pos_iff n o 0 k β E).mp (by linarith)
  · intro h
    apply strictAnti_nat_of_succ_lt
    intro m
    change egbFixedChargeAGibbsCollisionSignedDifference n o (m + 1) k β E <
      egbFixedChargeAGibbsCollisionSignedDifference n o m k β E
    have hs := (egbFixedChargeAGibbsCollisionSignedDifference_pos_iff n o m (k + 1) β E).mpr h
    rw [egbFixedChargeAGibbsCollisionSignedDifference_next_order] at hs
    linarith

end
end GaloisForLFunctions.HTGeometry
