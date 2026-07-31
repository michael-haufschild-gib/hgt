import GaloisForLFunctions.HTGeometry.MagnitudeBalancedWeight

/-!
# Positive jet-monomial degree means a derivative variable occurs

The magnitude-balanced weight theorems assume the anchor monomial has positive jet degree, and
that premise had no producer.  The jet degree is the total exponent carried by the derivative
variables, so positivity says exactly that some derivative variable occurs — and the simplest
monomial in one derivative variable realizes it.
-/

namespace GaloisForLFunctions

/-- **Positive jet degree is occurrence of a derivative variable.** -/
theorem jetMonomialDegree_pos_iff (n : ℕ) (m : Fin (n + 2) →₀ ℕ) :
    0 < jetMonomialDegree n m ↔ ∃ j : Fin (n + 1), m j.succ ≠ 0 := by
  rw [jetMonomialDegree, Nat.pos_iff_ne_zero, Ne, Finset.sum_eq_zero_iff]
  push Not
  simp

/-- The monomial in a single derivative variable has jet degree one. -/
theorem jetMonomialDegree_single (n : ℕ) (j : Fin (n + 1)) :
    jetMonomialDegree n (Finsupp.single j.succ 1) = 1 := by
  rw [jetMonomialDegree, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hk (Fin.succ_injective _ h).symm
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem jetMonomialDegree_pos_single (n : ℕ) (j : Fin (n + 1)) :
    0 < jetMonomialDegree n (Finsupp.single j.succ 1) := by
  rw [jetMonomialDegree_single]
  norm_num

/-- Hence the positive-degree premise is attained at every order. -/
theorem exists_jetMonomialDegree_pos (n : ℕ) :
    ∃ m : Fin (n + 2) →₀ ℕ, 0 < jetMonomialDegree n m :=
  ⟨Finsupp.single (Fin.succ 0) 1, jetMonomialDegree_pos_single n 0⟩

end GaloisForLFunctions
