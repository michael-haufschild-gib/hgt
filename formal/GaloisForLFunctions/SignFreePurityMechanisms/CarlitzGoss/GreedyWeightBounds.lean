import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopBlockFeasibility

/-!
# Weight bounds for divisible compositions

The greedy last part exceeds half the divisible total. Induction on the initial
composition therefore puts its weight strictly between the preceding multiple
of the total and the trivial upper bound. Every weight maximum satisfies the
same bounds, without yet identifying it with the greedy composition.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- For divisible total value, the greedy last part carries more than half the total. -/
theorem IsGreedy.last_gt_half {C : DigitComposition p s (k + 2) S}
    (hC : C.IsGreedy) (hp : 2 ≤ p) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    digitValue p S < 2 * C.value (Fin.last (k + 1)) := by
  obtain ⟨D, hD⟩ := C.exists_last_gt_half hp hN
  have hmax := hC.last_max D
  linarith only [hD, hmax]

/-- The weight of a greedy divisible composition lies above the preceding multiple of its total. -/
theorem greedy_weight_lower (m : ℕ) (hp : 2 ≤ p) :
    ∀ {S : Finset (Digit p)} (C : DigitComposition p s (m + 1) S), C.IsGreedy →
      ((p : ℤ) ^ s - 1) ∣ digitValue p S → (m : ℤ) * digitValue p S < C.weight := by
  induction m with
  | zero =>
    intro S C _ _
    simp only [Nat.cast_zero, zero_mul]
    simpa [weight] using C.value_pos (by omega : 0 < p) (0 : Fin 1)
  | succ m ih =>
    intro S C hC hN
    have hI := ih C.initial hC.initial C.initial_total_divisible
    have hhalf := hC.last_gt_half hp hN
    have htotal := digitValue_union C.prefix_disjoint_last
    rw [C.prefix_union_last] at htotal
    change digitValue p S = digitValue p (C.prefixDigits (m + 1)) + C.value (Fin.last (m + 1)) at htotal
    rw [htotal] at hhalf ⊢
    rw [C.weight_eq_initial_add_last]
    push_cast
    nlinarith only [hI, hhalf]

theorem IsOptimal.weight_lower {m : ℕ} {C : DigitComposition p s (m + 1) S}
    (hC : C.IsOptimal) (hp : 2 ≤ p) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    (m : ℤ) * digitValue p S < C.weight := by
  obtain ⟨G, hG⟩ := exists_greedy ⟨C⟩
  exact (greedy_weight_lower m hp G hG hN).trans_le (hC G)

/-- Adjacent-multiple bounds for the weight of an optimal or greedy divisible composition. -/
theorem weight_bounds_of_optimal_or_greedy {m : ℕ} {C : DigitComposition p s (m + 1) S}
    (hp : 2 ≤ p) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S)
    (hC : C.IsOptimal ∨ C.IsGreedy) :
    (m : ℤ) * digitValue p S < C.weight ∧ C.weight ≤ ((m + 1 : ℕ) : ℤ) * digitValue p S := by
  refine ⟨?_, C.weight_le (by omega)⟩
  rcases hC with hC | hC
  · exact hC.weight_lower hp hN
  · exact greedy_weight_lower m hp C hC hN

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.weight_bounds_of_optimal_or_greedy
