import GaloisForLFunctions.HTGeometry.PostcriticalEscapeUnconditional

/-!
# Distinct occupation states give distinct factors

Two different `m`-element subsets of a set of distinct roots give two different monic factors: a root
selected by one and not the other is a root of one factor and not of the other.

So the pure critical fibre really has as many points as there are occupation states, and its
cardinality is the critical binomial multiplicity rather than merely bounded by it.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- **Distinct occupation states give distinct selected factors.** -/
theorem criticalHorizonLeftFactorFromRoots_injective {m n : ℕ} {root : Fin (m + n) → K}
    (hroot : Function.Injective root) :
    Function.Injective (criticalHorizonLeftFactorFromRoots root :
      criticalHorizonOccupationStates m n → K[X]) := by
  classical
  intro S T hST
  by_contra hne
  have hsub : ¬ (S.1 ⊆ T.1) := by
    intro hsubset
    exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hsubset (by rw [S.2, T.2])))
  obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.1 hsub
  have h0 : (criticalHorizonLeftFactorFromRoots root S).eval (root j) = 0 := by
    rw [criticalHorizonLeftFactorFromRoots, Polynomial.eval_prod]
    refine Finset.prod_eq_zero hjS ?_
    simp
  have hne0 : (criticalHorizonLeftFactorFromRoots root T).eval (root j) ≠ 0 := by
    rw [criticalHorizonLeftFactorFromRoots, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 (fun i hi => ?_)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    intro hcon
    exact hjT (hroot (sub_eq_zero.1 hcon) ▸ hi)
  rw [hST] at h0
  exact hne0 h0

/-- **The pure critical fibre has at least the binomial multiplicity of points.**  The selected
factors of the distinct occupation states are pairwise distinct factorisations of `1 + t^L`. -/
theorem exists_injective_pureFactorisations (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hL : 0 < m + n) :
    ∃ f : criticalHorizonOccupationStates m n → K[X] × K[X],
      Function.Injective f ∧
      ∀ S, (f S).1 * (f S).2 = 1 + X ^ (m + n) ∧ (f S).1.Monic ∧ (f S).1.natDegree = m ∧
        (f S).2.Monic ∧ (f S).2.natDegree = n := by
  classical
  set root := pureCriticalRootLabeling (K := K) hL with hroot
  refine ⟨fun S => (criticalHorizonLeftFactorFromRoots root S,
    criticalHorizonRightFactorFromRoots root S), ?_, fun S => ?_⟩
  · intro S T hST
    exact criticalHorizonLeftFactorFromRoots_injective
      (pureCriticalRootLabeling_injective hL) (congrArg Prod.fst hST)
  · exact ⟨pureCriticalRootFactors_mul hL S, monic_criticalHorizonLeftFactorFromRoots root S,
      natDegree_criticalHorizonLeftFactorFromRoots root S,
      monic_criticalHorizonRightFactorFromRoots root S,
      natDegree_criticalHorizonRightFactorFromRoots root S⟩

end GaloisForLFunctions.HTGeometry
