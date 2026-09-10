import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsBinomialCollisionHistory

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem binomial_information_budget (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m)
    (hl : ∀ m, egbFixedChargeAGibbsCollisionExcess n m β E ≤ 4 * f m)
    (hu : ∀ m, f m ≤ (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E) :
    Summable (fun m : ℕ => ((m + k).choose k : ℝ) * f (m + 1)) ∧
      egbFixedChargeAGibbsBinomialCollisionBudget n k β E / 4 ≤
        (∑' m : ℕ, ((m + k).choose k : ℝ) * f (m + 1)) ∧
      (∑' m : ℕ, ((m + k).choose k : ℝ) * f (m + 1)) ≤
        (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsBinomialCollisionBudget n k β E := by
  have hc := egbFixedChargeAGibbsCollisionExcess_binomial_hasSum n k β E
  have hupper (m : ℕ) : ((m + k).choose k : ℝ) * f (m + 1) ≤
      (2 : ℝ) ^ (n + 3) *
        (((m + k).choose k : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) := by
    calc
      _ ≤ ((m + k).choose k : ℝ) *
          ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) :=
        mul_le_mul_of_nonneg_left (hu (m + 1)) (by positivity)
      _ = _ := by ring
  have hs : Summable (fun m : ℕ => ((m + k).choose k : ℝ) * f (m + 1)) :=
    (hc.summable.mul_left ((2 : ℝ) ^ (n + 3))).of_nonneg_of_le
      (fun m => mul_nonneg (by positivity) (hf (m + 1))) hupper
  refine ⟨hs, ?_, hasSum_le hupper hs.hasSum (hc.mul_left _)⟩
  have hlow : egbFixedChargeAGibbsBinomialCollisionBudget n k β E ≤
      4 * ∑' m : ℕ, ((m + k).choose k : ℝ) * f (m + 1) := by
    apply hasSum_le _ hc (hs.hasSum.mul_left 4)
    intro m
    calc
      _ ≤ ((m + k).choose k : ℝ) * (4 * f (m + 1)) :=
        mul_le_mul_of_nonneg_left (hl (m + 1)) (by positivity)
      _ = _ := by ring
  linarith

/-- Every entropy time moment is finite and lies between explicit multiples of the exact collision budget. -/
theorem egbFixedChargeAGibbsEntropyDeficit_binomial_budget (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m : ℕ => ((m + k).choose k : ℝ) * egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) ∧
      egbFixedChargeAGibbsBinomialCollisionBudget n k β E / 4 ≤
        (∑' m : ℕ, ((m + k).choose k : ℝ) * egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) ∧
      (∑' m : ℕ, ((m + k).choose k : ℝ) * egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) ≤
        (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsBinomialCollisionBudget n k β E := by
  apply binomial_information_budget n k β E (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E)
    (fun m => egbFixedChargeAGibbsEntropyDeficit_nonneg n m β E)
  · intro m
    have h := egbFixedChargeAGibbsEntropyDeficit_collision_lower n m β E
    linarith
  · exact fun m => egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E

/-- Every squared-Hellinger time moment satisfies the same finite spectral budget bounds. -/
theorem egbFixedChargeAGibbsHellingerSquared_binomial_budget (n k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m : ℕ => ((m + k).choose k : ℝ) * egbFixedChargeAGibbsHellingerSquared n (m + 1) β E) ∧
      egbFixedChargeAGibbsBinomialCollisionBudget n k β E / 4 ≤
        (∑' m : ℕ, ((m + k).choose k : ℝ) * egbFixedChargeAGibbsHellingerSquared n (m + 1) β E) ∧
      (∑' m : ℕ, ((m + k).choose k : ℝ) * egbFixedChargeAGibbsHellingerSquared n (m + 1) β E) ≤
        (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsBinomialCollisionBudget n k β E := by
  apply binomial_information_budget n k β E (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
    (fun m => sq_nonneg _)
    (fun m => egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m β E)
  exact fun m => (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E).trans
    (egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E)

end
end GaloisForLFunctions.HTGeometry
