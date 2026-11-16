import GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure

/-!
# Binary specialization of symmetric observations

At a binary string supported on `S`, the elementary symmetric polynomial
of degree `r` counts the `r`-subsets of `S`. This includes the vanishing
cutoff above `|S|` and gives the exact first-failure law for uniformly
permuted schedules with deterministic successes and failures.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry.FirstFailure
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section
variable {n : ℕ} {R : Type*} [CommRing R]

/-- The binary string with ones exactly on `S`. -/
def binaryCoordinates (S : Finset (Fin n)) (i : Fin n) : R := if i ∈ S then 1 else 0

private theorem prod_binaryCoordinates (S A : Finset (Fin n)) :
    (∏ i ∈ A, binaryCoordinates (R := R) S i) = if A ⊆ S then 1 else 0 := by
  classical
  by_cases h : A ⊆ S
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    exact if_pos (h hi)
  · rw [if_neg h]
    simp only [Finset.subset_iff] at h
    push Not at h
    obtain ⟨i, hi, hnot⟩ := h
    apply Finset.prod_eq_zero hi
    exact if_neg hnot

/-- Binary evaluation is the binomial counting law, over any commutative ring. -/
theorem esymm_binaryCoordinates (S : Finset (Fin n)) (r : ℕ) :
    esymm (binaryCoordinates (R := R) S) r = (S.card.choose r : R) := by
  classical
  unfold esymm
  simp_rw [prod_binaryCoordinates]
  rw [← Finset.sum_filter]
  have hfilter : ((Finset.univ : Finset (Fin n)).powersetCard r).filter
      (fun A => A ⊆ S) = S.powersetCard r := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, and_comm]
  rw [hfilter]
  simp

/-- Degrees above the number of ones vanish identically. -/
theorem esymm_binaryCoordinates_above (S : Finset (Fin n)) (r : ℕ) :
    esymm (binaryCoordinates (R := R) S) (S.card + r + 1) = 0 := by
  rw [esymm_binaryCoordinates, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- The existing permutation-averaged ledger becomes a difference of binomial ratios. -/
theorem binaryFirstFailure_exact {K : Type*} [Field K] [CharZero K]
    (S : Finset (Fin n)) (r : Fin n) :
    averagedFirstFailure (binaryCoordinates (R := K) S) r =
      (S.card.choose r.val : K) / (n.choose r.val : K) -
        (S.card.choose (r.val + 1) : K) / (n.choose (r.val + 1) : K) := by
  rw [averagedFirstFailure_eq_div_choose, esymm_binaryCoordinates, esymm_binaryCoordinates]

/-- The same specialization for the polynomial object used by the symmetric coefficient field. -/
theorem eval_esymm_binaryCoordinates (S : Finset (Fin n)) (r : ℕ) :
    MvPolynomial.eval (binaryCoordinates (R := R) S) (MvPolynomial.esymm (Fin n) R r) =
      (S.card.choose r : R) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X]
  exact esymm_binaryCoordinates S r

#print axioms esymm_binaryCoordinates
#print axioms esymm_binaryCoordinates_above
#print axioms binaryFirstFailure_exact
#print axioms eval_esymm_binaryCoordinates

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
