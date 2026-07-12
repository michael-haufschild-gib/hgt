import GaloisForLFunctions.WeightPolynomial

/-!
# The leading symbol can degenerate: a falling-factorial dependence

Within the fixed degree-and-order class `(r, O) = (4, 4)` the five weight polynomials live in
the four-dimensional space of degree-`4` polynomials divisible by `X`, so they are linearly
dependent.  An explicit dependence is

`(X)₃(X)₁ − 2(X)₂² + (X)₂(X)₁² = 0`

(`descPochhammer_class44_dependence`), equivalently the three same-class weight polynomials of
the differential monomials `Y₃Y₁Y₀²`, `Y₂²Y₀²`, `Y₂Y₁²Y₀` satisfy a nontrivial linear relation
(`weightPolynomial_class44_dependence`).

Consequently the differential polynomial `Y₃Y₁ − 2Y₂² + Y₂Y₁²` has a **vanishing leading
symbol**: at the balanced coefficient index its top-order contribution cancels.  So the
balanced-index / leading-symbol argument alone cannot establish hypertranscendence of a
superlacunary gap series — leading-symbol linear independence is false, and the proof must
descend to subleading order.
-/

open Polynomial

namespace GaloisForLFunctions

/-- The falling-factorial dependence in class `(4, 4)`. -/
theorem descPochhammer_class44_dependence :
    descPochhammer ℚ 3 * descPochhammer ℚ 1
      - 2 * (descPochhammer ℚ 2) ^ 2 + descPochhammer ℚ 2 * (descPochhammer ℚ 1) ^ 2 = 0 := by
  simp only [show (3 : ℕ) = 2 + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
    descPochhammer_succ_right, descPochhammer_zero]
  ring

/-- **Leading-symbol degeneracy.**  Three weight polynomials of the same degree-and-order class
`(4, 4)` are linearly dependent, so leading-symbol independence fails. -/
theorem weightPolynomial_class44_dependence :
    weightPolynomial (![3, 1, 0, 0] : Fin 4 → ℕ)
      - 2 * weightPolynomial (![2, 2, 0, 0] : Fin 4 → ℕ)
      + weightPolynomial (![2, 1, 1, 0] : Fin 4 → ℕ) = 0 := by
  have e1 : weightPolynomial (![3, 1, 0, 0] : Fin 4 → ℕ)
      = descPochhammer ℚ 3 * descPochhammer ℚ 1 := by
    simp [weightPolynomial, Fin.prod_univ_four, descPochhammer_zero]
  have e2 : weightPolynomial (![2, 2, 0, 0] : Fin 4 → ℕ) = (descPochhammer ℚ 2) ^ 2 := by
    simp [weightPolynomial, Fin.prod_univ_four, descPochhammer_zero]; ring
  have e3 : weightPolynomial (![2, 1, 1, 0] : Fin 4 → ℕ)
      = descPochhammer ℚ 2 * (descPochhammer ℚ 1) ^ 2 := by
    simp [weightPolynomial, Fin.prod_univ_four, descPochhammer_zero]; ring
  rw [e1, e2, e3]
  exact descPochhammer_class44_dependence

end GaloisForLFunctions
