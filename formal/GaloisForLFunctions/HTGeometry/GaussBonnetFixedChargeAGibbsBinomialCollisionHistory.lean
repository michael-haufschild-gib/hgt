import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsDominantInformationPrefactors
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# All-order temporal collision moments

The critical thermal kernel obtained from arXiv:2609.00025 gives exact
binomially weighted histories. These are moments of its mathematical Gibbs
relaxation law, not assertions of physical black-hole stochastic evolution.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The exact spectral budget for the binomial time moment of order `k`. -/
def egbFixedChargeAGibbsBinomialCollisionBudget (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  (4 / 9 : ℝ) / (5 / 9 : ℝ) ^ (k + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
    (1 / 36 : ℝ) / (35 / 36 : ℝ) ^ (k + 1) * egbFixedChargeAGibbsFastModeEnergy n β E

private theorem binomial_geometric_tail (k : ℕ) (r W : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun m : ℕ => ((m + k).choose k : ℝ) * r ^ (m + 1) * W)
      (r / (1 - r) ^ (k + 1) * W) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k hr).mul_right (r * W)
  have he : (fun m : ℕ => ((m + k).choose k : ℝ) * r ^ (m + 1) * W) =
      (fun m : ℕ => (((m + k).choose k : ℝ) * r ^ m) * (r * W)) := by
    funext m; rw [pow_succ r m]; ring
  have hv : r / (1 - r) ^ (k + 1) * W = (1 / (1 - r) ^ (k + 1)) * (r * W) := by ring
  rw [he, hv]
  exact h

/-- Every binomially weighted positive-time collision history has an exact two-sector sum. -/
theorem egbFixedChargeAGibbsCollisionExcess_binomial_hasSum (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => ((m + k).choose k : ℝ) *
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)
        (egbFixedChargeAGibbsBinomialCollisionBudget n k β E) := by
  have hA := binomial_geometric_tail k (4 / 9) (egbFixedChargeAGibbsSlowModeEnergy n β E) (by norm_num)
  have hB := binomial_geometric_tail k (1 / 36) (egbFixedChargeAGibbsFastModeEnergy n β E) (by norm_num)
  have ha : 1 - (4 / 9 : ℝ) = 5 / 9 := by norm_num
  have hb : 1 - (1 / 36 : ℝ) = 35 / 36 := by norm_num
  rw [ha] at hA
  rw [hb] at hB
  have he : (fun m : ℕ => ((m + k).choose k : ℝ) *
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) =
    (fun m : ℕ => ((m + k).choose k : ℝ) * (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
      ((m + k).choose k : ℝ) * (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) := by
    funext m; rw [egbFixedChargeAGibbsCollisionExcess_two_rate]; ring
  rw [he]
  exact hA.add hB

/-- Every time-moment budget is bounded by its exact slow-sector constant times initial collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_binomial_bound (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, ((m + k).choose k : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) ≤
      (4 / 9 : ℝ) / (5 / 9 : ℝ) ^ (k + 1) * egbFixedChargeAGibbsCollisionExcess n 0 β E := by
  have hs := egbFixedChargeAGibbsCollisionExcess_binomial_hasSum n k β E
  have ht := binomial_geometric_tail k (4 / 9) (egbFixedChargeAGibbsCollisionExcess n 0 β E) (by norm_num)
  have ha : 1 - (4 / 9 : ℝ) = 5 / 9 := by norm_num
  rw [ha] at ht
  rw [hs.tsum_eq]
  apply hasSum_le _ hs ht
  intro m
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (egbFixedChargeAGibbsCollisionExcess_spectral_bound n (m + 1) β E)
    (show (0 : ℝ) ≤ ((m + k).choose k : ℝ) by positivity)

/-- The actual positive slow Gibbs family attains every binomial time-moment bound. -/
theorem egbFixedChargeAGibbsSlow_collision_binomial_hasSum (n k : ℕ) :
    HasSum (fun m : ℕ => ((m + k).choose k : ℝ) *
      egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n))
        ((4 / 9 : ℝ) / (5 / 9 : ℝ) ^ (k + 1) *
          egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) := by
  have ht := binomial_geometric_tail k (4 / 9)
    (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) (by norm_num)
  have ha : 1 - (4 / 9 : ℝ) = 5 / 9 := by norm_num
  rw [ha] at ht
  have he : (fun m : ℕ => ((m + k).choose k : ℝ) *
      egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n)) =
    (fun m : ℕ => ((m + k).choose k : ℝ) * (4 / 9 : ℝ) ^ (m + 1) *
      egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) := by
    funext m; rw [egbFixedChargeAGibbsSlow_collision_exact n (m + 1)]; ring
  rw [he]
  exact ht

/-- The uniform coefficient for each binomial time moment is optimal across all Gibbs inputs. -/
theorem egbFixedChargeAGibbsCollisionExcess_binomial_sharp (n k : ℕ) (B : ℝ) :
    (∀ (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ),
      (∑' m : ℕ, ((m + k).choose k : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) ≤
        B * egbFixedChargeAGibbsCollisionExcess n 0 β E) ↔
          (4 / 9 : ℝ) / (5 / 9 : ℝ) ^ (k + 1) ≤ B := by
  constructor
  · intro h
    have hw := h 1 (egbFixedChargeAGibbsSlowEnergy n)
    rw [(egbFixedChargeAGibbsSlow_collision_binomial_hasSum n k).tsum_eq] at hw
    nlinarith [egbFixedChargeAGibbsSlow_collision_initial_pos n]
  · intro h β E
    exact (egbFixedChargeAGibbsCollisionExcess_binomial_bound n k β E).trans
      (mul_le_mul_of_nonneg_right h (egbFixedChargeAGibbsCollisionExcess_nonneg n 0 β E))

/-- The first time moment is an exact weighted sum of slow and fast spectral energies. -/
theorem egbFixedChargeAGibbsCollisionExcess_time_hasSum (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => (m : ℝ) * egbFixedChargeAGibbsCollisionExcess n m β E)
      ((36 / 25 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (36 / 1225 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E) := by
  have hA := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (4 / 9 : ℝ)) (by norm_num)).mul_right
    (egbFixedChargeAGibbsSlowModeEnergy n β E)
  have hB := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 36 : ℝ)) (by norm_num)).mul_right
    (egbFixedChargeAGibbsFastModeEnergy n β E)
  norm_num at hA hB
  have he : (fun m : ℕ => (m : ℝ) * egbFixedChargeAGibbsCollisionExcess n m β E) =
    (fun m : ℕ => (m : ℝ) * (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (m : ℝ) * (1 / 36 : ℝ) ^ m * egbFixedChargeAGibbsFastModeEnergy n β E) := by
    funext m
    cases m with
    | zero => simp
    | succ m => rw [egbFixedChargeAGibbsCollisionExcess_two_rate]; ring
  rw [he]
  exact hA.add hB

end
end GaloisForLFunctions.HTGeometry
