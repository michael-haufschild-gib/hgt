import Mathlib

/-!
# The leading-symbol weight polynomial of a differential monomial

For derivative orders `j : Fin r → ℕ`, the **weight polynomial** `∏ₜ descPochhammer ℚ (jₜ)`
is monic of degree `∑ₜ jₜ` (`weightPolynomial_monic`, `weightPolynomial_natDegree`), and its
value at a natural source `s` is the product of falling factorials `∏ₜ descFactorial s jₜ`
(`weightPolynomial_eval_nat`) — exactly the extraction weight of the differential monomial
`∏ₜ f^{(jₜ)}` at a uniform source `s`.

The degree of the weight polynomial is the total derivative order, so differential monomials of
different total order carry weight polynomials of different degree.  The non-degeneracy of a
differential polynomial's leading symbol — whether these weight polynomials, indexed by
order-multiset within a fixed degree and total order, are linearly independent — is the
remaining algebraic obstruction to full hypertranscendence of a superlacunary gap series.
-/

open Polynomial

namespace GaloisForLFunctions

/-- The leading-symbol weight polynomial of derivative orders `j`. -/
noncomputable def weightPolynomial {r : ℕ} (j : Fin r → ℕ) : Polynomial ℚ :=
  ∏ t, descPochhammer ℚ (j t)

/-- The weight polynomial is monic. -/
theorem weightPolynomial_monic {r : ℕ} (j : Fin r → ℕ) : (weightPolynomial j).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun t _ => monic_descPochhammer ℚ (j t)

/-- The weight polynomial has degree equal to the total derivative order. -/
theorem weightPolynomial_natDegree {r : ℕ} (j : Fin r → ℕ) :
    (weightPolynomial j).natDegree = ∑ t, j t := by
  rw [weightPolynomial,
    Polynomial.natDegree_prod _ _ fun t _ => (monic_descPochhammer ℚ (j t)).ne_zero]
  exact Finset.sum_congr rfl fun t _ => descPochhammer_natDegree ℚ (j t)

/-- The weight polynomial evaluated at a natural source is the product of falling factorials —
the extraction weight of the differential monomial at a uniform source. -/
theorem weightPolynomial_eval_nat {r : ℕ} (j : Fin r → ℕ) (s : ℕ) :
    (weightPolynomial j).eval (s : ℚ) = ∏ t, (Nat.descFactorial s (j t) : ℚ) := by
  rw [weightPolynomial, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun t _ => descPochhammer_eval_eq_descFactorial ℚ s (j t)

/-- **Evaluation support.**  The weight polynomial is nonzero at a natural source `s` exactly
when `s` reaches every derivative order — so its least nonzero integer evaluation is at the
maximal order `maxₜ jₜ`.  This is the triangulation datum for the leading-symbol independence:
a differential monomial's leading symbol first activates at the source equal to its top order. -/
theorem weightPolynomial_eval_nat_ne_zero_iff {r : ℕ} (j : Fin r → ℕ) (s : ℕ) :
    (weightPolynomial j).eval (s : ℚ) ≠ 0 ↔ ∀ t, j t ≤ s := by
  rw [weightPolynomial_eval_nat, Finset.prod_ne_zero_iff]
  constructor
  · intro h t
    have ht := h t (Finset.mem_univ t)
    rwa [Nat.cast_ne_zero, ne_eq, Nat.descFactorial_eq_zero_iff_lt, not_lt] at ht
  · intro h t _
    rw [Nat.cast_ne_zero, ne_eq, Nat.descFactorial_eq_zero_iff_lt, not_lt]
    exact h t

end GaloisForLFunctions
