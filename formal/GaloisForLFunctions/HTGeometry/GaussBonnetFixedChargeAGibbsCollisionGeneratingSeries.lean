import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsWeightedInformationHistory

/-!
# Exact Gibbs collision generating series

The two spectral energies separate genuine singularities from canceled modes.
In particular a fast-only input crosses the slow-sector convergence boundary.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Closed generating value, with each spectral contribution kept separate to retain cancellations. -/
def egbFixedChargeAGibbsCollisionGeneratingValue (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  egbFixedChargeAGibbsCollisionExcess n 0 β E +
    (q ^ 2 * (4 / 9)) / (1 - q ^ 2 * (4 / 9)) * egbFixedChargeAGibbsSlowModeEnergy n β E +
    (q ^ 2 * (1 / 36)) / (1 - q ^ 2 * (1 / 36)) * egbFixedChargeAGibbsFastModeEnergy n β E

private theorem geometric_mode_hasSum (t a : ℝ) (ht : 0 ≤ t) (ha : a = 0 ∨ t < 1) :
    HasSum (fun m : ℕ => t ^ (m + 1) * a) (t / (1 - t) * a) := by
  rcases ha with ha | ha
  · subst a
    simpa using (hasSum_geometric_of_lt_one (r := (0 : ℝ)) (by norm_num) (by norm_num)).mul_right (0 : ℝ)
  · have h := (hasSum_geometric_of_lt_one ht ha).mul_right (t * a)
    have he : (fun m : ℕ => t ^ (m + 1) * a) = (fun m : ℕ => t ^ m * (t * a)) := by
      funext m; rw [pow_succ t m]; ring
    have hv : t / (1 - t) * a = (1 - t)⁻¹ * (t * a) := by ring
    rw [he, hv]
    exact h

private theorem generating_hasSum (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hq : q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E < 1) :
    HasSum (fun m : ℕ => (q ^ 2) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E)
      (egbFixedChargeAGibbsCollisionGeneratingValue n β q E) := by
  have hA : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ q ^ 2 * (4 / 9 : ℝ) < 1 := by
    by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
    · exact Or.inl ha
    · exact Or.inr (by simpa [egbFixedChargeAGibbsDominantCollisionRate, ha] using hq)
  have hB : egbFixedChargeAGibbsFastModeEnergy n β E = 0 ∨ q ^ 2 * (1 / 36 : ℝ) < 1 := by
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · exact Or.inl hb
    · right
      by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
      · simpa [egbFixedChargeAGibbsDominantCollisionRate, ha, hb] using hq
      · have hs := hA.resolve_left ha
        have hm := mul_le_mul_of_nonneg_left (show (1 / 36 : ℝ) ≤ 4 / 9 by norm_num) (sq_nonneg q)
        linarith
  have hs := (geometric_mode_hasSum (q ^ 2 * (4 / 9))
    (egbFixedChargeAGibbsSlowModeEnergy n β E) (by positivity) hA).add
      (geometric_mode_hasSum (q ^ 2 * (1 / 36))
        (egbFixedChargeAGibbsFastModeEnergy n β E) (by positivity) hB)
  have he : (fun m : ℕ => (q ^ 2) ^ (m + 1) *
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) =
    (fun m : ℕ => (q ^ 2 * (4 / 9 : ℝ)) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (q ^ 2 * (1 / 36 : ℝ)) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) := by
    funext m
    rw [egbFixedChargeAGibbsCollisionExcess_two_rate, mul_pow, mul_pow]
    ring
  rw [← he] at hs
  have ht := (hasSum_nat_add_iff
    (f := fun m : ℕ => (q ^ 2) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E) 1).mp hs
  simp only [Finset.sum_range_one, pow_zero, one_mul] at ht
  have hv : egbFixedChargeAGibbsCollisionGeneratingValue n β q E =
      (q ^ 2 * (4 / 9)) / (1 - q ^ 2 * (4 / 9)) * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (q ^ 2 * (1 / 36)) / (1 - q ^ 2 * (1 / 36)) * egbFixedChargeAGibbsFastModeEnergy n β E +
      egbFixedChargeAGibbsCollisionExcess n 0 β E := by
    unfold egbFixedChargeAGibbsCollisionGeneratingValue
    ring
  rw [hv]
  exact ht

/-- The spectral rational expression is the actual sum exactly inside the input-selected convergence domain. -/
theorem egbFixedChargeAGibbsCollisionExcess_generating_hasSum_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => (q ^ 2) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E)
      (egbFixedChargeAGibbsCollisionGeneratingValue n β q E) ↔
        q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E < 1 :=
  ⟨fun h => (egbFixedChargeAGibbsCollisionExcess_weighted_summable_iff n β q E).mp h.summable,
    generating_hasSum n β q E⟩

/-- The slow-mode boundary is removable exactly when the slow Fourier energy vanishes. -/
theorem egbFixedChargeAGibbsCollisionExcess_slow_boundary_hasSum_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => (9 / 4 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E)
      (egbFixedChargeAGibbsCollisionExcess n 0 β E + egbFixedChargeAGibbsFastModeEnergy n β E / 15) ↔
        egbFixedChargeAGibbsSlowModeEnergy n β E = 0 := by
  have h := egbFixedChargeAGibbsCollisionExcess_generating_hasSum_iff n β (3 / 2) E
  have hv : egbFixedChargeAGibbsCollisionGeneratingValue n β (3 / 2) E =
      egbFixedChargeAGibbsCollisionExcess n 0 β E + egbFixedChargeAGibbsFastModeEnergy n β E / 15 := by
    unfold egbFixedChargeAGibbsCollisionGeneratingValue
    norm_num
    ring
  rw [hv] at h
  norm_num at h
  rw [h]
  unfold egbFixedChargeAGibbsDominantCollisionRate
  split_ifs <;> norm_num <;> assumption

/-- At the fast-mode boundary, only inputs equilibrating after one step have summable weighted histories. -/
theorem egbFixedChargeAGibbsCollisionExcess_fast_boundary_summable_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m : ℕ => (36 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E) ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧ egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  have h := egbFixedChargeAGibbsCollisionExcess_weighted_summable_iff n β 6 E
  norm_num at h
  rw [h]
  unfold egbFixedChargeAGibbsDominantCollisionRate
  split_ifs <;> simp_all <;> norm_num

end
end GaloisForLFunctions.HTGeometry
