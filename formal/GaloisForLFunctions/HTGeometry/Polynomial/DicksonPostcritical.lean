import GaloisForLFunctions.HTGeometry.Polynomial.DicksonCriticalFibers

/-!
# The finite postcritical set of normalized Chebyshev maps

The differential identity confines critical values to `2` and `-2`.
Both endpoints map back into this pair, so every positive critical orbit
is contained in a fixed finite set, independently of the degree.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The positive endpoint is fixed in every degree. -/
theorem dicksonMap_two (n : ℕ) : dicksonMap n 2 = 2 := by
  have h := dicksonMap_joukowski n (w := 1) one_ne_zero
  norm_num at h
  exact h

/-- The negative endpoint records the parity of the degree. -/
theorem dicksonMap_neg_two (n : ℕ) : dicksonMap n (-2) = 2 * (-1 : ℂ) ^ n := by
  have h := dicksonMap_joukowski n (w := -1) (neg_ne_zero.mpr one_ne_zero)
  rcases neg_one_pow_eq_or ℂ n with hn | hn <;> norm_num [hn] at h ⊢ <;> exact h

/-- The two possible critical values form a forward-invariant set. -/
theorem dicksonMap_endpoints_invariant (n : ℕ) :
    Set.MapsTo (dicksonMap n) {2, -2} {2, -2} := by
  intro z hz
  rcases hz with rfl | rfl
  · exact Or.inl (dicksonMap_two n)
  · rw [dicksonMap_neg_two]
    rcases neg_one_pow_eq_or ℂ n with h | h
    · exact Or.inl (by rw [h, mul_one])
    · exact Or.inr (by change 2 * (-1 : ℂ) ^ n = -2; rw [h, mul_neg_one])

/-- Every positive iterate of a critical point lies in the endpoint pair. -/
theorem dicksonMap_critical_iterates (n k : ℕ) :
    Set.MapsTo (dicksonMap (n + 1))^[k + 1]
      {z | (Polynomial.dickson 1 (1 : ℂ) (n + 1)).derivative.eval z = 0} {2, -2} := by
  intro z hz
  rw [Function.iterate_succ_apply]
  exact (dicksonMap_endpoints_invariant (n + 1)).iterate k (dicksonMap_critical_values n hz)

/-- The union of all positive critical orbits is finite in every positive degree. -/
theorem dicksonMap_postcritical_finite (n : ℕ) :
    Set.Finite {w : ℂ | ∃ z : ℂ, ∃ k : ℕ,
      (Polynomial.dickson 1 (1 : ℂ) (n + 1)).derivative.eval z = 0 ∧
        (dicksonMap (n + 1))^[k + 1] z = w} := by
  apply (Set.toFinite ({2, -2} : Set ℂ)).subset
  rintro w ⟨z, k, hz, rfl⟩
  exact dicksonMap_critical_iterates n k hz

end GaloisForLFunctions.HTGeometry
