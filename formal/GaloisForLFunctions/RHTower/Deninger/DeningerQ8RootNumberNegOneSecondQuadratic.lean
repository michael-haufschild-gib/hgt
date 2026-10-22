import GaloisForLFunctions.RHTower.Deninger.DeningerQ8RootNumberNegOneFirstQuadratic

/-!
# Second quadratic field in the root-number-minus-one Q8 witness

This module proves the second required nonsquare statement on the concrete
first field: `41` has no square root in `ℚ(√5)`.  It then constructs the
literal degree-two extension adjoining `√41`.

The proof does not import an abstract degree argument.  It expands a putative
square in the verified `1, √5` normal form, compares both coefficients using
the established coordinate rigidity, and discharges the resulting rational
square cases with explicit integer-square bounds.
-/

open Polynomial

namespace RHTower

noncomputable section

theorem deningerQ8RootNumberNegOne_nat_fortyOne_not_square : ¬ IsSquare (41 : ℕ) := by
  rintro ⟨n, hn⟩
  by_cases hle : n ≤ 6
  · have hnle : n * n ≤ 6 * 6 := Nat.mul_le_mul hle hle
    have : 41 ≤ 6 * 6 := by rw [hn]; exact hnle
    norm_num at this
  · have hge : 7 ≤ n := by omega
    have hnge : 7 * 7 ≤ n * n := Nat.mul_le_mul hge hge
    have : 7 * 7 ≤ 41 := by rw [hn]; exact hnge
    norm_num at this

theorem deningerQ8RootNumberNegOne_fortyOne_not_square (q : ℚ) : q ^ (2 : ℕ) ≠ 41 := by
  intro h
  apply deningerQ8RootNumberNegOne_nat_fortyOne_not_square
  apply Rat.isSquare_natCast_iff.mp
  exact ⟨q, by simpa [pow_two] using h.symm⟩

theorem deningerQ8RootNumberNegOne_nat_twoHundredFive_not_square : ¬ IsSquare (205 : ℕ) := by
  rintro ⟨n, hn⟩
  by_cases hle : n ≤ 14
  · have hnle : n * n ≤ 14 * 14 := Nat.mul_le_mul hle hle
    have : 205 ≤ 14 * 14 := by rw [hn]; exact hnle
    norm_num at this
  · have hge : 15 ≤ n := by omega
    have hnge : 15 * 15 ≤ n * n := Nat.mul_le_mul hge hge
    have : 15 * 15 ≤ 205 := by rw [hn]; exact hnge
    norm_num at this

theorem deningerQ8RootNumberNegOne_twoHundredFive_not_square (q : ℚ) : q ^ (2 : ℕ) ≠ 205 := by
  intro h
  apply deningerQ8RootNumberNegOne_nat_twoHundredFive_not_square
  apply Rat.isSquare_natCast_iff.mp
  exact ⟨q, by simpa [pow_two] using h.symm⟩

/-- The second literal radicand has no square root in the constructed first
quadratic field. -/
theorem deningerQ8RootNumberNegOne_fortyOne_not_square_in_firstQuadratic
    (w : deningerQ8RootNumberNegOneFirstQuadraticField) : w ^ (2 : ℕ) ≠ 41 := by
  intro hw
  obtain ⟨a, b, hab⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form w
  have hscalarCast :
      ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 41 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) =
        (a : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) +
          5 * (b : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) - 41 := by
    change AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial
        (a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 41) =
      (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a) ^ (2 : ℕ) +
        5 * (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial b) ^ (2 : ℕ) - 41
    rw [map_sub, map_add, map_mul, map_pow, map_pow]
    norm_num
  have hcrossCast :
      ((2 * a * b : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) =
        2 * (a : deningerQ8RootNumberNegOneFirstQuadraticField) *
          (b : deningerQ8RootNumberNegOneFirstQuadraticField) := by
    change AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial (2 * a * b) =
      2 * AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a *
        AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial b
    rw [map_mul, map_mul]
    norm_num
  have hcoord :
      ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 41 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) +
          (2 * a * b : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot = 0 := by
    calc
      ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 41 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) +
          (2 * a * b : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot =
          ((a : deningerQ8RootNumberNegOneFirstQuadraticField) +
            b * deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ (2 : ℕ) - 41 := by
        calc
          ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 41 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) +
              (2 * a * b : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot =
              ((a : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) +
                2 * (a : deningerQ8RootNumberNegOneFirstQuadraticField) *
                  (b : deningerQ8RootNumberNegOneFirstQuadraticField) *
                    deningerQ8RootNumberNegOneFirstQuadraticRoot +
                (b : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) *
                  deningerQ8RootNumberNegOneFirstQuadraticRoot ^ (2 : ℕ)) - 41 := by
            rw [hscalarCast, hcrossCast,
              deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
            ring
          _ = ((a : deningerQ8RootNumberNegOneFirstQuadraticField) +
              b * deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ (2 : ℕ) - 41 := by
            ring
      _ = 0 := by rw [← hab, hw]; ring
  rcases deningerQ8RootNumberNegOneFirstQuadratic_coordinates_eq_zero hcoord with
    ⟨hscalar, hcross⟩
  have hab0 : a * b = 0 := by
    have : (2 : ℚ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hcross)).resolve_left this
  rcases mul_eq_zero.mp hab0 with ha | hb
  · apply deningerQ8RootNumberNegOne_twoHundredFive_not_square (5 * b)
    calc
      (5 * b) ^ (2 : ℕ) = 5 * (5 * b ^ (2 : ℕ)) := by ring
      _ = 5 * 41 := by
        have hbsq : 5 * b ^ (2 : ℕ) = 41 := by
          rw [ha] at hscalar
          linarith
        rw [hbsq]
      _ = 205 := by norm_num
  · apply deningerQ8RootNumberNegOne_fortyOne_not_square a
    rw [hb] at hscalar
    linarith

/-- The second quadratic polynomial in the explicit Q8 radical tower. -/
def deningerQ8RootNumberNegOneSecondQuadraticPolynomial :
    deningerQ8RootNumberNegOneFirstQuadraticField[X] := X ^ (2 : ℕ) - C 41

theorem deningerQ8RootNumberNegOne_secondQuadratic_irreducible :
    Irreducible deningerQ8RootNumberNegOneSecondQuadraticPolynomial := by
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two
    deningerQ8RootNumberNegOne_fortyOne_not_square_in_firstQuadratic

noncomputable instance :
    Fact (Irreducible deningerQ8RootNumberNegOneSecondQuadraticPolynomial) :=
  ⟨deningerQ8RootNumberNegOne_secondQuadratic_irreducible⟩

/-- The concrete field `ℚ(√5, √41)` in the radical tower. -/
abbrev deningerQ8RootNumberNegOneSecondQuadraticField :=
  AdjoinRoot deningerQ8RootNumberNegOneSecondQuadraticPolynomial

/-- Literal `√41` in the constructed second field. -/
def deningerQ8RootNumberNegOneSecondQuadraticRoot :
    deningerQ8RootNumberNegOneSecondQuadraticField :=
  AdjoinRoot.root deningerQ8RootNumberNegOneSecondQuadraticPolynomial

theorem deningerQ8RootNumberNegOneSecondQuadraticRoot_sq :
    deningerQ8RootNumberNegOneSecondQuadraticRoot ^ (2 : ℕ) = 41 := by
  have h := AdjoinRoot.eval₂_root deningerQ8RootNumberNegOneSecondQuadraticPolynomial
  rw [deningerQ8RootNumberNegOneSecondQuadraticPolynomial, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_C] at h
  change (AdjoinRoot.root (X ^ (2 : ℕ) - C
    (41 : deningerQ8RootNumberNegOneFirstQuadraticField))) ^ (2 : ℕ) =
      (41 : AdjoinRoot (X ^ (2 : ℕ) - C (41 : deningerQ8RootNumberNegOneFirstQuadraticField)))
  calc
    (AdjoinRoot.root (X ^ (2 : ℕ) - C
        (41 : deningerQ8RootNumberNegOneFirstQuadraticField))) ^ (2 : ℕ) =
        AdjoinRoot.of (X ^ (2 : ℕ) - C
          (41 : deningerQ8RootNumberNegOneFirstQuadraticField))
          (41 : deningerQ8RootNumberNegOneFirstQuadraticField) := sub_eq_zero.mp h
    _ = 41 := (map_natCast (AdjoinRoot.of (X ^ (2 : ℕ) - C
      (41 : deningerQ8RootNumberNegOneFirstQuadraticField))) 41).symm

theorem deningerQ8RootNumberNegOneSecondQuadraticField_finrank :
    Module.finrank deningerQ8RootNumberNegOneFirstQuadraticField
      deningerQ8RootNumberNegOneSecondQuadraticField = 2 := by
  rw [PowerBasis.finrank]
  rw [AdjoinRoot.powerBasis_dim
    deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero]
  norm_num [deningerQ8RootNumberNegOneSecondQuadraticPolynomial]

/-- `205` remains nonsquare in `ℚ(√5)`.  This auxiliary arithmetic gate is
the norm obstruction for the final radical of the Q8 witness. -/
theorem deningerQ8RootNumberNegOne_twoHundredFive_not_square_in_firstQuadratic
    (w : deningerQ8RootNumberNegOneFirstQuadraticField) : w ^ (2 : ℕ) ≠ 205 := by
  intro hw
  obtain ⟨a, b, hab⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form w
  have hscalarCast :
      ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 205 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) =
        (a : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) +
          5 * (b : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) - 205 := by
    change AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial
        (a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 205) =
      (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a) ^ (2 : ℕ) +
        5 * (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial b) ^ (2 : ℕ) - 205
    rw [map_sub, map_add, map_mul, map_pow, map_pow]
    norm_num
  have hcrossCast :
      ((2 * a * b : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) =
        2 * (a : deningerQ8RootNumberNegOneFirstQuadraticField) *
          (b : deningerQ8RootNumberNegOneFirstQuadraticField) := by
    change AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial (2 * a * b) =
      2 * AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a *
        AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial b
    rw [map_mul, map_mul]
    norm_num
  have hcoord :
      ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 205 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) +
          (2 * a * b : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot = 0 := by
    calc
      ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 205 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) +
          (2 * a * b : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot =
          ((a : deningerQ8RootNumberNegOneFirstQuadraticField) +
            b * deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ (2 : ℕ) - 205 := by
        calc
          ((a ^ (2 : ℕ) + 5 * b ^ (2 : ℕ) - 205 : ℚ) : deningerQ8RootNumberNegOneFirstQuadraticField) +
              (2 * a * b : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot =
              ((a : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) +
                2 * (a : deningerQ8RootNumberNegOneFirstQuadraticField) *
                  (b : deningerQ8RootNumberNegOneFirstQuadraticField) *
                    deningerQ8RootNumberNegOneFirstQuadraticRoot +
                (b : deningerQ8RootNumberNegOneFirstQuadraticField) ^ (2 : ℕ) *
                  deningerQ8RootNumberNegOneFirstQuadraticRoot ^ (2 : ℕ)) - 205 := by
            rw [hscalarCast, hcrossCast,
              deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
            ring
          _ = ((a : deningerQ8RootNumberNegOneFirstQuadraticField) +
              b * deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ (2 : ℕ) - 205 := by ring
      _ = 0 := by rw [← hab, hw]; ring
  rcases deningerQ8RootNumberNegOneFirstQuadratic_coordinates_eq_zero hcoord with
    ⟨hscalar, hcross⟩
  have hab0 : a * b = 0 := by
    have : (2 : ℚ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hcross)).resolve_left this
  rcases mul_eq_zero.mp hab0 with ha | hb
  · apply deningerQ8RootNumberNegOne_fortyOne_not_square b
    rw [ha] at hscalar
    have : 5 * b ^ (2 : ℕ) = 205 := by linarith
    calc
      b ^ (2 : ℕ) = 205 / 5 := by linarith
      _ = 41 := by norm_num
  · apply deningerQ8RootNumberNegOne_twoHundredFive_not_square a
    rw [hb] at hscalar
    linarith

/-- Every element of `ℚ(√5, √41)` has its literal two-coordinate normal form
over the first quadratic field. -/
theorem deningerQ8RootNumberNegOneSecondQuadratic_normal_form
    (w : deningerQ8RootNumberNegOneSecondQuadraticField) :
    ∃ a b : deningerQ8RootNumberNegOneFirstQuadraticField,
      w = a + b * deningerQ8RootNumberNegOneSecondQuadraticRoot := by
  let f := deningerQ8RootNumberNegOneSecondQuadraticPolynomial
  have hf : f.Monic := by
    dsimp [f, deningerQ8RootNumberNegOneSecondQuadraticPolynomial]
    exact monic_X_pow_sub_C (41 : deningerQ8RootNumberNegOneFirstQuadraticField) (by norm_num)
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective w
  let p : deningerQ8RootNumberNegOneFirstQuadraticField[X] := q %ₘ f
  have hpdeg : p.degree ≤ 1 := by
    have hlt : p.degree < (2 : WithBot ℕ) := by
      calc
        p.degree < f.degree := Polynomial.degree_modByMonic_lt q hf
        _ = 2 := by
          simp [f, deningerQ8RootNumberNegOneSecondQuadraticPolynomial,
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
  simp [p, f, deningerQ8RootNumberNegOneSecondQuadraticRoot]
  ring

end

end RHTower
