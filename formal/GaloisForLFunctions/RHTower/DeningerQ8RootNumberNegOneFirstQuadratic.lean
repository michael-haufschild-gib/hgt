import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.AdjoinRoot

/-!
# First quadratic field in the root-number-minus-one Q8 witness

This module constructs the first genuine field in the explicit radical tower
for the documented Q8 root-number-minus-one witness.  It proves `5` is not a
square in `ℚ`, hence `X² - 5` is irreducible, and uses `AdjoinRoot` to obtain a
degree-two field carrying a literal root with square `5`.

The remaining two nonsquare gates, the normality argument, the Q8 Galois-group
identification, and the root-number calculation are not assumed here.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- The first quadratic polynomial in the explicit Q8 radical tower. -/
def deningerQ8RootNumberNegOneFirstQuadraticPolynomial : ℚ[X] := X ^ 2 - C 5

/-- `5` is not a square in `ℚ`; the proof reduces a hypothetical rational
square to the primality obstruction in `ℕ`. -/
theorem deningerQ8RootNumberNegOne_five_not_square (q : ℚ) : q ^ 2 ≠ 5 := by
  intro h
  apply Nat.prime_five.not_isSquare
  apply Rat.isSquare_natCast_iff.mp
  exact ⟨q, by simpa [pow_two] using h.symm⟩

/-- Irreducibility of the literal first quadratic. -/
theorem deningerQ8RootNumberNegOne_firstQuadratic_irreducible :
    Irreducible deningerQ8RootNumberNegOneFirstQuadraticPolynomial := by
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two
    deningerQ8RootNumberNegOne_five_not_square

noncomputable instance :
    Fact (Irreducible deningerQ8RootNumberNegOneFirstQuadraticPolynomial) :=
  ⟨deningerQ8RootNumberNegOne_firstQuadratic_irreducible⟩

/-- The first actual field in the radical tower. -/
abbrev deningerQ8RootNumberNegOneFirstQuadraticField :=
  AdjoinRoot deningerQ8RootNumberNegOneFirstQuadraticPolynomial

/-- Literal `√5` in the constructed first field. -/
def deningerQ8RootNumberNegOneFirstQuadraticRoot :
    deningerQ8RootNumberNegOneFirstQuadraticField :=
  AdjoinRoot.root deningerQ8RootNumberNegOneFirstQuadraticPolynomial

/-- The canonical adjoined root squares to the literal first radicand. -/
theorem deningerQ8RootNumberNegOneFirstQuadraticRoot_sq :
    deningerQ8RootNumberNegOneFirstQuadraticRoot ^ 2 = 5 := by
  have h := AdjoinRoot.eval₂_root deningerQ8RootNumberNegOneFirstQuadraticPolynomial
  rw [deningerQ8RootNumberNegOneFirstQuadraticPolynomial, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_C] at h
  change (AdjoinRoot.root (X ^ 2 - C (5 : ℚ))) ^ 2 =
    (5 : AdjoinRoot (X ^ 2 - C (5 : ℚ)))
  calc
    (AdjoinRoot.root (X ^ 2 - C (5 : ℚ))) ^ 2 =
        AdjoinRoot.of (X ^ 2 - C (5 : ℚ)) (5 : ℚ) := sub_eq_zero.mp h
    _ = 5 := (map_natCast (AdjoinRoot.of (X ^ 2 - C (5 : ℚ))) 5).symm

/-- Exact degree of the first field in the radical tower. -/
theorem deningerQ8RootNumberNegOneFirstQuadraticField_finrank :
    Module.finrank ℚ deningerQ8RootNumberNegOneFirstQuadraticField = 2 := by
  rw [PowerBasis.finrank]
  rw [AdjoinRoot.powerBasis_dim
    deningerQ8RootNumberNegOne_firstQuadratic_irreducible.ne_zero]
  norm_num [deningerQ8RootNumberNegOneFirstQuadraticPolynomial]

/-- Every element of the first quadratic field has its exact two-coordinate
normal form in the literal basis `1, √5`. -/
theorem deningerQ8RootNumberNegOneFirstQuadratic_normal_form
    (w : deningerQ8RootNumberNegOneFirstQuadraticField) :
    ∃ a b : ℚ,
      w = a + b * deningerQ8RootNumberNegOneFirstQuadraticRoot := by
  let f := deningerQ8RootNumberNegOneFirstQuadraticPolynomial
  have hf : f.Monic := by
    dsimp [f, deningerQ8RootNumberNegOneFirstQuadraticPolynomial]
    exact monic_X_pow_sub_C (5 : ℚ) (by norm_num)
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective w
  let p : ℚ[X] := q %ₘ f
  have hpdeg : p.degree ≤ 1 := by
    have hlt : p.degree < (2 : WithBot ℕ) := by
      calc
        p.degree < f.degree := Polynomial.degree_modByMonic_lt q hf
        _ = 2 := by
          simp [f, deningerQ8RootNumberNegOneFirstQuadraticPolynomial,
            Polynomial.degree_X_pow_sub_C]
    by_cases hp : p = 0
    · simp [hp]
    rw [Polynomial.degree_eq_natDegree hp] at hlt ⊢
    have hlt' : p.natDegree < 2 := by exact_mod_cast hlt
    exact_mod_cast Nat.le_of_lt_succ hlt'
  refine ⟨p.coeff 0, p.coeff 1, ?_⟩
  rw [← AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f q)]
  rw [AdjoinRoot.modByMonicHom_mk]
  change AdjoinRoot.mk f p = _
  rw [Polynomial.eq_X_add_C_of_degree_le_one hpdeg]
  simp [p, f, deningerQ8RootNumberNegOneFirstQuadraticRoot]
  ring

/-- The constructed `√5` is not the image of any rational. -/
theorem deningerQ8RootNumberNegOneFirstQuadraticRoot_not_rational (q : ℚ) :
    deningerQ8RootNumberNegOneFirstQuadraticRoot ≠ q := by
  intro h
  have hsq := congrArg
    (fun u : deningerQ8RootNumberNegOneFirstQuadraticField => u ^ 2) h
  rw [deningerQ8RootNumberNegOneFirstQuadraticRoot_sq] at hsq
  apply deningerQ8RootNumberNegOne_five_not_square q
  apply (algebraMap ℚ deningerQ8RootNumberNegOneFirstQuadraticField).injective
  simpa using hsq.symm

/-- The literal basis `1, √5` has no nontrivial rational relation. -/
theorem deningerQ8RootNumberNegOneFirstQuadratic_coordinates_eq_zero
    {a b : ℚ}
    (h : (a : deningerQ8RootNumberNegOneFirstQuadraticField) +
        b * deningerQ8RootNumberNegOneFirstQuadraticRoot = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · constructor
    · apply (algebraMap ℚ deningerQ8RootNumberNegOneFirstQuadraticField).injective
      simpa [hb] using h
    · exact hb
  · have hb' : (b : deningerQ8RootNumberNegOneFirstQuadraticField) ≠ 0 := by
      intro hbzero
      apply hb
      apply (algebraMap ℚ deningerQ8RootNumberNegOneFirstQuadraticField).injective
      simpa using hbzero
    have hroot : deningerQ8RootNumberNegOneFirstQuadraticRoot =
        -((a : deningerQ8RootNumberNegOneFirstQuadraticField) /
          (b : deningerQ8RootNumberNegOneFirstQuadraticField)) := by
      rw [← neg_div]
      apply (eq_div_iff hb').2
      linear_combination h
    exfalso
    apply (deningerQ8RootNumberNegOneFirstQuadraticRoot_not_rational (-(a / b)))
    convert hroot using 1
    change AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial (-(a / b)) =
      -(AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a /
        AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial b)
    rw [map_neg]
    exact congrArg Neg.neg
      (map_div₀ (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial) a b)

end

end RHTower
