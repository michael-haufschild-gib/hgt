import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsWeightedCollisionHistory

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem weighted_summable_iff_collision (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m)
    (hl : ∀ m, egbFixedChargeAGibbsCollisionExcess n m β E ≤ 4 * f m)
    (hu : ∀ m, f m ≤ (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E) :
    Summable (fun m : ℕ => (q ^ (2 : ℕ)) ^ m * f m) ↔
      Summable (fun m : ℕ => (q ^ (2 : ℕ)) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E) := by
  constructor
  · intro hs
    apply (hs.mul_left 4).of_nonneg_of_le
    · intro m
      exact mul_nonneg (by positivity) (egbFixedChargeAGibbsCollisionExcess_nonneg n m β E)
    · intro m
      calc
        _ ≤ (q ^ (2 : ℕ)) ^ m * (4 * f m) := mul_le_mul_of_nonneg_left (hl m) (by positivity)
        _ = _ := by ring
  · intro hs
    apply (hs.mul_left ((2 : ℝ) ^ (n + 3))).of_nonneg_of_le
    · intro m; exact mul_nonneg (by positivity) (hf m)
    · intro m
      calc
        _ ≤ (q ^ (2 : ℕ)) ^ m * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E) :=
          mul_le_mul_of_nonneg_left (hu m) (by positivity)
        _ = _ := by ring

/-- Weighted entropy history converges exactly below the surviving spectral threshold. -/
theorem egbFixedChargeAGibbsEntropyDeficit_weighted_summable_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m : ℕ => (q ^ (2 : ℕ)) ^ m * egbFixedChargeAGibbsEntropyDeficit n m β E) ↔
      q ^ (2 : ℕ) * egbFixedChargeAGibbsDominantCollisionRate n β E < 1 := by
  rw [weighted_summable_iff_collision n β q E _
    (fun m => egbFixedChargeAGibbsEntropyDeficit_nonneg n m β E)
    (fun m => by have h := egbFixedChargeAGibbsEntropyDeficit_collision_lower n m β E; linarith)
    (fun m => egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E)]
  exact egbFixedChargeAGibbsCollisionExcess_weighted_summable_iff n β q E

/-- Weighted squared-Hellinger history has precisely the same convergence boundary. -/
theorem egbFixedChargeAGibbsHellingerSquared_weighted_summable_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m : ℕ => (q ^ (2 : ℕ)) ^ m * egbFixedChargeAGibbsHellingerSquared n m β E) ↔
      q ^ (2 : ℕ) * egbFixedChargeAGibbsDominantCollisionRate n β E < 1 := by
  rw [weighted_summable_iff_collision n β q E
    (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
    (fun m => sq_nonneg _)
    (fun m => egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m β E)
    (fun m => (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E).trans
      (egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E))]
  exact egbFixedChargeAGibbsCollisionExcess_weighted_summable_iff n β q E

end
end GaloisForLFunctions.HTGeometry
