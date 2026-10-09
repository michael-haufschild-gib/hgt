import GaloisForLFunctions.HTGeometry.VandermondeSign
import GaloisForLFunctions.HTGeometry.PaperMonicLeadingSubstitution

/-!
# Universal Vandermonde regularity over every commutative base ring

Every difference of distinct universal variables has a unit leading
coefficient. Their product is therefore cancellable even when the base
ring has zero divisors. This supplies uniqueness for integral alternant
division in the source normal-coordinate application.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped MonomialOrder BigOperators

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

private theorem paperLex_single_lt {i j : Fin n} (h : i < j) :
    (Finsupp.single j 1 : Fin n →₀ ℕ) ≺[MonomialOrder.lex] Finsupp.single i 1 := by
  change ∃ k : Fin n, (∀ l, l < k →
    (Finsupp.single j 1 : Fin n →₀ ℕ) l = (Finsupp.single i 1 : Fin n →₀ ℕ) l) ∧
    (Finsupp.single j 1 : Fin n →₀ ℕ) k < (Finsupp.single i 1 : Fin n →₀ ℕ) k
  refine ⟨i, ?_, ?_⟩
  · intro l hl
    simp only [Finsupp.single_apply, if_neg (ne_of_gt (lt_trans hl h)), if_neg (ne_of_gt hl)]
  · simp [h.ne]

/-- A universal root difference is regular over every commutative coefficient ring. -/
theorem paperVariableDifference_regular {i j : Fin n} (h : i < j) :
    IsRegular (X j - X i : MvPolynomial (Fin n) K) := by
  classical
  rcases subsingleton_or_nontrivial K with hK | hK
  · letI := hK
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · letI := hK
    have hlt : MonomialOrder.lex.degree (X j : MvPolynomial (Fin n) K) ≺[MonomialOrder.lex]
        MonomialOrder.lex.degree (X i : MvPolynomial (Fin n) K) := by
      rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
      exact paperLex_single_lt n h
    have hl : MonomialOrder.lex.leadingCoeff (X j - X i : MvPolynomial (Fin n) K) = -1 := by
      rw [← neg_sub (X i) (X j), MonomialOrder.leadingCoeff_neg,
        MonomialOrder.leadingCoeff_sub_of_lt hlt, MonomialOrder.leadingCoeff_X]
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    apply MonomialOrder.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
      (m := MonomialOrder.lex)
    rw [hl]
    exact isUnit_neg_one.mem_nonZeroDivisors

/-- The existing Vandermonde product on the universal root coordinates. -/
def paperUniversalVandermonde : MvPolynomial (Fin n) K :=
  vandermondeProd (X : Fin n → MvPolynomial (Fin n) K)

/-- Universal Vandermonde cancellation needs no domain or characteristic hypothesis. -/
theorem paperUniversalVandermonde_regular : IsRegular (paperUniversalVandermonde K n) := by
  unfold paperUniversalVandermonde vandermondeProd
  exact IsRegular.prod fun i _ => IsRegular.prod fun j hj =>
    paperVariableDifference_regular K n (Finset.mem_Ioi.mp hj)

/-- The universal Vandermonde obeys the native permutation-sign law over every base ring. -/
theorem paperUniversalVandermonde_rename (e : Equiv.Perm (Fin n)) :
    rename e (paperUniversalVandermonde K n) =
      (Equiv.Perm.sign e : ℤ) • paperUniversalVandermonde K n := by
  have h : rename e (paperUniversalVandermonde K n) =
      vandermondeProd ((X : Fin n → MvPolynomial (Fin n) K) ∘ e) := by
    simp only [paperUniversalVandermonde, vandermondeProd, map_prod, map_sub, rename_X,
      Function.comp_apply]
  rw [h, vandermondeProd_comp]
  rfl

end

end GaloisForLFunctions.HTGeometry
