import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneTopRadicand

/-!
# The literal Serre quaternionic radical field

The `DeningerQ8RootNumberNegOne` tower is a source-attested `Q8` root-number
minus-one witness, although its global epsilon calculation is not yet in Lean.
This leaf formalizes a traditional Serre radical presentation, the root field of

`X^(8 : ℕ) - 205 X^(6 : ℕ) + 13940 X^(4 : ℕ) - 378225 X^(2 : ℕ) + 3404025`.

This leaf constructs another degree-eight radical tower.  Its top
generator is `sqrt ((5 + sqrt 5) * (41 + sqrt 205))`; dividing that generator
by two gives the displayed Serre polynomial.  The proof here is wholly
algebraic: the top radicand is nonsquare by a relative-norm descent to the
already-proved nonsquareness of `41` in `ℚ(sqrt 5)`.

No equality between this radical presentation and the `41 + 6 * sqrt 41`
presentation is asserted in this file.

The global Artin epsilon-factor calculation proving root number `-1` remains a
separate, genuinely analytic-arithmetic formalization obligation.
-/

open Polynomial

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

/-- `5 + √5`, the first factor of Serre's actual top radicand. -/
def serreQ8TopR : K1 := 5 + deningerQ8RootNumberNegOneFirstQuadraticRoot

/-- `41 + √205`, written in the fixed literal `ℚ(√5,√41)` tower. -/
def serreQ8TopS : K2 :=
  ((41 : K1) : K2) +
    (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) *
      deningerQ8RootNumberNegOneSecondQuadraticRoot

/-- The `√41`-conjugate of `41 + √205`. -/
def serreQ8TopSConj : K2 :=
  ((41 : K1) : K2) -
    (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) *
      deningerQ8RootNumberNegOneSecondQuadraticRoot

theorem serreQ8_secondConjugation_topS :
    deningerQ8RootNumberNegOneSecondConjugation serreQ8TopS = serreQ8TopSConj := by
  simpa [serreQ8TopS, serreQ8TopSConj] using
    deningerQ8RootNumberNegOne_secondConjugation_normal
      (41 : K1) deningerQ8RootNumberNegOneFirstQuadraticRoot

/-- The relative norm of `41 + √205` is `1476 = 36 * 41`. -/
theorem serreQ8_topS_mul_conj : serreQ8TopS * serreQ8TopSConj = 1476 := by
  letI : CharZero K2 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
  unfold serreQ8TopS serreQ8TopSConj
  calc
    (((41 : K1) : K2) + (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) *
        deningerQ8RootNumberNegOneSecondQuadraticRoot) *
      (((41 : K1) : K2) - (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) *
        deningerQ8RootNumberNegOneSecondQuadraticRoot) =
        ((41 : K1) : K2) ^ (2 : ℕ) -
          (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) ^ (2 : ℕ) *
            deningerQ8RootNumberNegOneSecondQuadraticRoot ^ (2 : ℕ) := by ring
    _ = ((41 : K1) : K2) ^ (2 : ℕ) -
          (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) ^ (2 : ℕ) * 41 := by
      rw [deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
    _ = 1476 := by
      have h41 : ((41 : K1) : K2) = (41 : K2) := by
        change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          ((41 : ℕ) : K1) = (41 : K2)
        exact (map_natCast
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 41).symm
      have h5 : (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) ^ (2 : ℕ) =
          (5 : K2) := by
        rw [← map_pow, deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
        exact (map_natCast
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm
      rw [h41, h5]
      norm_num

theorem serreQ8_oneThousandFourHundredSeventySix_not_square_in_firstQuadratic
    (a : K1) : a ^ (2 : ℕ) ≠ 1476 := by
  intro ha
  letI : CharZero K1 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K1).injective
  apply deningerQ8RootNumberNegOne_fortyOne_not_square_in_firstQuadratic (a / 6)
  calc
    (a / 6) ^ (2 : ℕ) = a ^ (2 : ℕ) / (6 : K1) ^ (2 : ℕ) := by rw [div_pow]
    _ = 1476 / (6 : K1) ^ (2 : ℕ) := by rw [ha]
    _ = 41 := by
      rw [show (6 : K1) ^ (2 : ℕ) = 36 by norm_num]
      apply (div_eq_iff (by norm_num : (36 : K1) ≠ 0)).2
      norm_num

/-- The literal top radicand for the actual Serre root-number witness. -/
def serreQ8TopRadicand : K2 := (serreQ8TopR : K2) * serreQ8TopS

theorem serreQ8_secondConjugation_topRadicand :
    deningerQ8RootNumberNegOneSecondConjugation serreQ8TopRadicand =
      (serreQ8TopR : K2) * serreQ8TopSConj := by
  unfold serreQ8TopRadicand
  rw [map_mul, deningerQ8RootNumberNegOne_secondConjugation_of,
    serreQ8_secondConjugation_topS]

theorem serreQ8_topRadicand_mul_conj :
    serreQ8TopRadicand * deningerQ8RootNumberNegOneSecondConjugation serreQ8TopRadicand =
      (1476 : K2) * (serreQ8TopR : K2) ^ (2 : ℕ) := by
  rw [serreQ8_secondConjugation_topRadicand]
  change (serreQ8TopR : K2) * serreQ8TopS * ((serreQ8TopR : K2) * serreQ8TopSConj) =
    1476 * (serreQ8TopR : K2) ^ (2 : ℕ)
  calc
    (serreQ8TopR : K2) * serreQ8TopS * ((serreQ8TopR : K2) * serreQ8TopSConj) =
        (serreQ8TopR : K2) ^ (2 : ℕ) * (serreQ8TopS * serreQ8TopSConj) := by ring
    _ = 1476 * (serreQ8TopR : K2) ^ (2 : ℕ) := by
      rw [serreQ8_topS_mul_conj]
      ring

theorem serreQ8_topR_ne_zero : serreQ8TopR ≠ 0 := by
  intro h
  letI : CharZero K1 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K1).injective
  have hroot : deningerQ8RootNumberNegOneFirstQuadraticRoot = -5 := by
    dsimp [serreQ8TopR] at h
    linear_combination h
  have hs := deningerQ8RootNumberNegOneFirstQuadraticRoot_sq
  rw [hroot] at hs
  norm_num at hs

/-- Serre's top radicand is nonsquare in `ℚ(√5,√41)`. -/
theorem serreQ8_topRadicand_not_square (w : K2) : w ^ (2 : ℕ) ≠ serreQ8TopRadicand := by
  intro hw
  let r : K2 := serreQ8TopR
  let n : K2 := w * deningerQ8RootNumberNegOneSecondConjugation w
  let v : K2 := n / r
  have hr : r ≠ 0 := by
    intro hr
    apply serreQ8_topR_ne_zero
    apply (algebraMap K1 K2).injective
    simpa [r] using hr
  have hn_sq : n ^ (2 : ℕ) = 1476 * r ^ (2 : ℕ) := by
    unfold n
    calc
      (w * deningerQ8RootNumberNegOneSecondConjugation w) ^ (2 : ℕ) =
          w ^ (2 : ℕ) * (deningerQ8RootNumberNegOneSecondConjugation w) ^ (2 : ℕ) := by ring
      _ = serreQ8TopRadicand *
          deningerQ8RootNumberNegOneSecondConjugation serreQ8TopRadicand := by
        have hconj : (deningerQ8RootNumberNegOneSecondConjugation w) ^ (2 : ℕ) =
            deningerQ8RootNumberNegOneSecondConjugation serreQ8TopRadicand := by
          rw [← map_pow, hw]
        rw [hw, hconj]
      _ = 1476 * r ^ (2 : ℕ) := by
        simpa [r] using serreQ8_topRadicand_mul_conj
  have hv_sq : v ^ (2 : ℕ) = 1476 := by
    unfold v
    rw [div_pow, hn_sq]
    field_simp
  have hn_fixed : deningerQ8RootNumberNegOneSecondConjugation n = n := by
    unfold n
    rw [map_mul, deningerQ8RootNumberNegOne_secondConjugation_involutive]
    ring
  have hr_fixed : deningerQ8RootNumberNegOneSecondConjugation r = r := by
    unfold r serreQ8TopR
    exact deningerQ8RootNumberNegOne_secondConjugation_of _
  have hv_fixed : deningerQ8RootNumberNegOneSecondConjugation v = v := by
    unfold v
    rw [map_div₀, hn_fixed, hr_fixed]
  obtain ⟨a, ha⟩ :=
    deningerQ8RootNumberNegOne_secondConjugation_fixed_descent v hv_fixed
  apply serreQ8_oneThousandFourHundredSeventySix_not_square_in_firstQuadratic a
  apply (algebraMap K1 K2).injective
  calc
    algebraMap K1 K2 (a ^ (2 : ℕ)) = (a : K2) ^ (2 : ℕ) := by exact map_pow _ a 2
    _ = v ^ (2 : ℕ) := by rw [ha]
    _ = 1476 := hv_sq
    _ = algebraMap K1 K2 (1476 : K1) := by
      change (1476 : K2) = algebraMap K1 K2 ((1476 : ℕ) : K1)
      exact (map_natCast (algebraMap K1 K2) 1476).symm

/-- The final quadratic polynomial of the literal Serre degree-eight field. -/
def serreQ8ThirdQuadraticPolynomial : K2[X] := X ^ (2 : ℕ) - C serreQ8TopRadicand

theorem serreQ8_thirdQuadratic_irreducible : Irreducible serreQ8ThirdQuadraticPolynomial := by
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two serreQ8_topRadicand_not_square

noncomputable instance : Fact (Irreducible serreQ8ThirdQuadraticPolynomial) :=
  ⟨serreQ8_thirdQuadratic_irreducible⟩

/-- Serre's actual degree-eight quaternionic number field. -/
abbrev SerreQ8TopField := AdjoinRoot serreQ8ThirdQuadraticPolynomial

/-- The unscaled radical generator. -/
def serreQ8TopRoot : SerreQ8TopField := AdjoinRoot.root serreQ8ThirdQuadraticPolynomial

theorem serreQ8TopRoot_sq : serreQ8TopRoot ^ (2 : ℕ) = serreQ8TopRadicand := by
  have h := AdjoinRoot.eval₂_root serreQ8ThirdQuadraticPolynomial
  rw [serreQ8ThirdQuadraticPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem serreQ8TopField_finrank_over_second : Module.finrank K2 SerreQ8TopField = 2 := by
  rw [PowerBasis.finrank]
  rw [AdjoinRoot.powerBasis_dim serreQ8_thirdQuadratic_irreducible.ne_zero]
  norm_num [serreQ8ThirdQuadraticPolynomial]

theorem serreQ8SecondQuadraticField_finrank_over_rat : Module.finrank ℚ K2 = 4 := by
  rw [← Module.finrank_mul_finrank ℚ K1 K2]
  rw [deningerQ8RootNumberNegOneFirstQuadraticField_finrank,
    deningerQ8RootNumberNegOneSecondQuadraticField_finrank]

/-- Exact degree of Serre's literal witness field over `ℚ`. -/
theorem serreQ8TopField_finrank_over_rat : Module.finrank ℚ SerreQ8TopField = 8 := by
  rw [← Module.finrank_mul_finrank ℚ K2 SerreQ8TopField]
  rw [serreQ8SecondQuadraticField_finrank_over_rat, serreQ8TopField_finrank_over_second]

end

end RHTower
