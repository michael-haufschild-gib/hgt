import GaloisForLFunctions.RHTower.PrimeWordSupportSelector

/-!
# Marked-support diagonalization of a finite quadratic incidence

The marked Koszul support character is one on singleton support and zero on mixed support.  Applied
to ordered pairs of labels, it therefore converts the full quadratic incidence sum into the sum of
the diagonal squares.  This provides the exact finite combinatorial diagonalization needed by a
quadratic reflection-anomaly construction; it does not construct the source-side orbit labels or
the anomaly itself.
-/

namespace GaloisForLFunctions

section

variable {α : Type*} [DecidableEq α]

/-- The marked-support character of the two-label incidence `{i,j}`. -/
def markedPairSupportExponent (i j : α) : ℤ :=
  koszulSupportMarkedExponent ({i, j} : Finset α).card

/-- A pair incidence survives exactly on the diagonal. -/
theorem markedPairSupportExponent_eq (i j : α) :
    markedPairSupportExponent i j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [markedPairSupportExponent] using koszulSupportMarkedExponent_one
  · have hcard : ({i, j} : Finset α).card = 2 := by simp [hij]
    rw [markedPairSupportExponent, hcard,
      koszulSupportMarkedExponent_eq_zero (by omega), if_neg hij]

/-- **Finite quadratic diagonalization.**  Marking the active label support removes every
cross-label term and retains every diagonal square with coefficient one. -/
theorem markedSupport_diagonalizes_quadratic_sum
    (S : Finset α) (w : α → ℤ) :
    (∑ i ∈ S, ∑ j ∈ S,
      w i * w j * markedPairSupportExponent i j) =
      ∑ i ∈ S, (w i) ^ 2 := by
  simp only [markedPairSupportExponent_eq]
  calc
    (∑ i ∈ S, ∑ j ∈ S, w i * w j * if i = j then 1 else 0) =
        ∑ i ∈ S, w i * w i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · exact fun hiNot => (hiNot hi).elim
    _ = ∑ i ∈ S, (w i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

end

end GaloisForLFunctions
