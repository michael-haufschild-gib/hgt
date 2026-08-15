import GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation

/-!
# Extracting a solved relation from a failed Baker family

Failure of the `Option`-indexed inhomogeneous family produces an algebraic coefficient relation.
Its logarithmic part has a nonzero pivot; otherwise the constant coefficient also vanishes.
Normalizing at that pivot constructs `SolvedRelation` without changing any chosen logarithm branch.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

private def inhomogeneousFamily {n : ℕ} (lambda : Fin n → ℂ) :
    Option (Fin n) → ℂ
  | none => 1
  | some i => lambda i

theorem exists_solvedRelation_of_explicit_relation
    {n : ℕ} (lambda : Fin n → ℂ)
    (hexp : ∀ i, IsAlgebraic ℚ (Complex.exp (lambda i)))
    (hind : LinearIndependent ℚ lambda)
    (a : Option (Fin n) → ℂ) (ha : ∀ j, IsAlgebraic ℚ (a j))
    (hrel : ∑ j, a j * inhomogeneousFamily lambda j = 0)
    (hne : ∃ j, a j ≠ 0) :
    ∃ R : SolvedRelation, R.n = n := by
  have hpivot : ∃ i : Fin n, a (some i) ≠ 0 := by
    by_contra hnot
    push Not at hnot
    have hnone : a none = 0 := by
      rw [Fintype.sum_option] at hrel
      simp only [inhomogeneousFamily, mul_one] at hrel
      simp only [hnot, zero_mul, Finset.sum_const_zero, add_zero] at hrel
      exact hrel
    obtain ⟨j, hj⟩ := hne
    cases j with
    | none => exact hj hnone
    | some i => exact hj (hnot i)
  obtain ⟨pivot, hpivot⟩ := hpivot
  let constantCoeff : ℂ := -a none / a (some pivot)
  let coeff : {i : Fin n // i ≠ pivot} → ℂ :=
    fun i => -a (some i) / a (some pivot)
  have hconstantAlg : IsAlgebraic ℚ constantCoeff := by
    dsimp [constantCoeff]
    simpa [div_eq_mul_inv] using (ha none).neg.mul (ha (some pivot)).inv
  have hcoeffAlg : ∀ i, IsAlgebraic ℚ (coeff i) := by
    intro i
    dsimp [coeff]
    simpa [div_eq_mul_inv] using (ha (some i)).neg.mul (ha (some pivot)).inv
  have hpivotEq : lambda pivot = constantCoeff +
      ∑ i : {i : Fin n // i ≠ pivot}, coeff i * lambda i := by
    rw [Fintype.sum_option, Fintype.sum_eq_add_sum_subtype_ne _ pivot] at hrel
    simp only [inhomogeneousFamily, mul_one] at hrel
    dsimp [constantCoeff, coeff]
    apply mul_left_cancel₀ hpivot
    calc
      a (some pivot) * lambda pivot =
          -(a none + ∑ i : {i : Fin n // i ≠ pivot},
            a (some i) * lambda i) := by
        linear_combination hrel
      _ = a (some pivot) *
          (-a none / a (some pivot) +
            ∑ i : {i : Fin n // i ≠ pivot},
              (-a (some i) / a (some pivot)) * lambda i) := by
        rw [mul_add, Finset.mul_sum]
        field_simp [hpivot]
        rw [neg_add, Finset.sum_neg_distrib]
  let R : SolvedRelation :=
    { n := n
      lambda := lambda
      exp_algebraic := hexp
      lambda_independent := hind
      pivot := pivot
      constantCoeff := constantCoeff
      coeff := coeff
      constantCoeff_algebraic := hconstantAlg
      coeff_algebraic := hcoeffAlg
      pivot_eq := hpivotEq }
  exact ⟨R, rfl⟩

theorem exists_solvedRelation_of_not_full_linearIndependent
    {n : ℕ} (lambda : Fin n → ℂ)
    (hexp : ∀ i, IsAlgebraic ℚ (Complex.exp (lambda i)))
    (hind : LinearIndependent ℚ lambda)
    (hnot : ¬ LinearIndependent (algebraicClosure ℚ ℂ)
      (inhomogeneousFamily lambda)) :
    ∃ R : SolvedRelation, R.n = n := by
  rw [Fintype.linearIndependent_iff] at hnot
  push Not at hnot
  obtain ⟨b, hsum, j, hj⟩ := hnot
  let a : Option (Fin n) → ℂ := fun i => (b i : ℂ)
  have ha : ∀ i, IsAlgebraic ℚ (a i) := by
    intro i
    exact mem_algebraicClosure_iff.mp (b i).property
  have hrel : ∑ i, a i * inhomogeneousFamily lambda i = 0 := by
    simpa [a, IntermediateField.smul_def, smul_eq_mul] using hsum
  have hne : a j ≠ 0 := by
    intro hz
    apply hj
    apply Subtype.ext
    exact hz
  exact exists_solvedRelation_of_explicit_relation lambda hexp hind a ha hrel ⟨j, hne⟩

end GaloisForLFunctions.RHTower.BakerGeneralProof
