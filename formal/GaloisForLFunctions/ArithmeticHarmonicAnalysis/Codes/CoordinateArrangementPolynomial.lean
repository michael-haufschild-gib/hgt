import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Recovering the face numbers from the point-count polynomial

Andrusov's Theorem 46 expands each torus stratum in the ordinary monomial
basis. Translation back by one recovers the number of faces of each
codimension. The same polynomial therefore tests exactly what the counts
over all finite alphabets can distinguish.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset Polynomial
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Integral counting polynomial in the alphabet size. -/
def arrangementPolynomial (K : Finset (Finset ι)) : ℤ[X] :=
  ∑ s ∈ K, (X - 1) ^ (Fintype.card ι - s.card)

/-- The ordinary coefficients are the signed binomial transform of the face numbers. -/
theorem coeff_arrangementPolynomial (K : Finset (Finset ι)) (k : ℕ) :
    (arrangementPolynomial K).coeff k =
      ∑ s ∈ K, (-1 : ℤ) ^ (Fintype.card ι - s.card - k) *
        ((Fintype.card ι - s.card).choose k : ℤ) := by
  simp only [arrangementPolynomial, finsetSum_coeff]
  refine sum_congr rfl fun s _ => ?_
  simpa only [map_neg, C_1, sub_eq_add_neg] using
    (coeff_X_add_C_pow (-1 : ℤ) (Fintype.card ι - s.card) k)

/-- Evaluating at the field order counts actual rational points in the complement. -/
theorem eval_arrangementPolynomial {F : Type*} [Field F] [Fintype F]
    (K : Finset (Finset ι)) :
    (arrangementPolynomial K).eval (Fintype.card F : ℤ) =
      ((arrangementWords (fun _ : ι => ({0} : Finset F)) K).card : ℤ) := by
  rw [card_pointArrangement]
  have hF : 1 ≤ Fintype.card F := Fintype.card_pos
  simp [arrangementPolynomial, Polynomial.eval_finsetSum, Nat.cast_sub hF]

/-- Translation to the torus-size variable recovers a polynomial with nonnegative coefficients. -/
theorem arrangementPolynomial_translate (K : Finset (Finset ι)) :
    (arrangementPolynomial K).comp (X + 1) = ∑ s ∈ K, X ^ (Fintype.card ι - s.card) := by
  simp [arrangementPolynomial, Polynomial.sum_comp, Polynomial.pow_comp, Polynomial.sub_comp]

/-- Each translated coefficient recovers a whole codimension layer, including empty layers. -/
theorem coeff_arrangementPolynomial_translate (K : Finset (Finset ι)) (d : ℕ) :
    ((arrangementPolynomial K).comp (X + 1)).coeff d =
      ((K.filter fun s : Finset ι => Fintype.card ι - s.card = d).card : ℤ) := by
  rw [arrangementPolynomial_translate, finsetSum_coeff]
  simp [coeff_X_pow, sum_boole, eq_comm]

/-- Two face families give the same counting polynomial precisely when they have
the same number of faces in every codimension. -/
theorem arrangementPolynomial_eq_iff {κ : Type*} [Fintype κ]
    (K : Finset (Finset ι)) (L : Finset (Finset κ)) :
    arrangementPolynomial K = arrangementPolynomial L ↔ ∀ d,
      (K.filter fun s : Finset ι => Fintype.card ι - s.card = d).card =
      (L.filter fun s : Finset κ => Fintype.card κ - s.card = d).card := by
  constructor
  · intro h d
    have he := congrArg (fun P : ℤ[X] => (P.comp (X+1)).coeff d) h
    change ((arrangementPolynomial K).comp (X+1)).coeff d =
      ((arrangementPolynomial L).comp (X+1)).coeff d at he
    rw [coeff_arrangementPolynomial_translate, coeff_arrangementPolynomial_translate] at he
    exact_mod_cast he
  · intro h
    have ht : (arrangementPolynomial K).comp (X+1) = (arrangementPolynomial L).comp (X+1) := by
      ext d
      rw [coeff_arrangementPolynomial_translate, coeff_arrangementPolynomial_translate, h d]
    have hc := congrArg (fun p : ℤ[X] => p.comp (X-1)) ht
    simpa [Polynomial.comp_assoc, Polynomial.add_comp] using hc

/-- Disjoint families of patterns contribute additively, including all overlaps by inclusion-exclusion. -/
theorem arrangementPolynomial_union_add_inter (K L : Finset (Finset ι)) :
    arrangementPolynomial (K ∪ L) + arrangementPolynomial (K ∩ L) =
      arrangementPolynomial K + arrangementPolynomial L := by
  exact sum_union_inter

/-- Deleting a face removes exactly the torus stratum of its codimension. -/
theorem arrangementPolynomial_insert (s : Finset ι) (K : Finset (Finset ι)) :
    arrangementPolynomial (insert s K) = (X-1)^(Fintype.card ι - s.card) +
      arrangementPolynomial (K.erase s) := by
  unfold arrangementPolynomial
  calc
    _ = ∑ t ∈ insert s (K.erase s), (X-1 : ℤ[X]) ^ (Fintype.card ι-t.card) := by
      have he : insert s K = insert s (K.erase s) := by
        ext t
        by_cases h : t = s <;> simp [h]
      rw [he]
    _ = _ := sum_insert (notMem_erase _ _)

#print axioms coeff_arrangementPolynomial
#print axioms eval_arrangementPolynomial
#print axioms arrangementPolynomial_eq_iff
#print axioms arrangementPolynomial_union_add_inter
#print axioms arrangementPolynomial_insert

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
