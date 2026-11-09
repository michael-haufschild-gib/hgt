import GaloisForLFunctions.HTGeometry.MonicDiscriminantProducts
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Prime-quadratic discriminants

The polynomial attached to a positive integer is the product of `X²+p`
over its prime factors, with multiplicity. Its discriminant records both
repeated prime factors and the orientation of the distinct quadratic factors.
The definition uses factorization alone.
-/

noncomputable section
open Polynomial ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HTGeometry

/-- An integral imaginary quadratic factor when its parameter is positive. -/
def arithmeticQuadratic (p : ℤ) : ℤ[X] := X ^ 2 + C p

theorem arithmeticQuadratic_monic (p : ℤ) : (arithmeticQuadratic p).Monic := by
  exact monic_X_pow_add_C p (by decide : 2 ≠ 0)

theorem arithmeticQuadratic_natDegree (p : ℤ) : (arithmeticQuadratic p).natDegree = 2 := by
  exact natDegree_X_pow_add_C

/-- The negative quadratic discriminant is obtained from the integral equation. -/
theorem arithmeticQuadratic_discr (p : ℤ) : (arithmeticQuadratic p).discr = -4 * p := by
  rw [discr_of_degree_eq_two]
  · simp only [arithmeticQuadratic, coeff_add, coeff_X_pow, coeff_C]
    norm_num
  · exact degree_X_pow_add_C (by decide : 0 < 2) p

/-- Distinct parameters meet with the square of their difference. -/
theorem arithmeticQuadratic_resultant (p q : ℤ) :
    resultant (arithmeticQuadratic p) (arithmeticQuadratic q) = (q - p) ^ 2 := by
  have h : arithmeticQuadratic q = C (q-p) + arithmeticQuadratic p * 1 := by
    simp only [arithmeticQuadratic, map_sub, mul_one]
    ring
  rw [h, monic_resultant_add_mul (arithmeticQuadratic_monic p), resultant_C_right]
  simp only [natDegree_C, pow_zero, one_mul, arithmeticQuadratic_natDegree]

/-- The monic polynomial retaining every prime factor, including repetitions. -/
def quadraticFactorProduct (s : List ℤ) : ℤ[X] := (s.map arithmeticQuadratic).prod

/-- All pairwise parameter differences, with their list orientation. -/
def quadraticVandermonde : List ℤ → ℤ
  | [] => 1
  | p :: s => (s.map (fun q => q-p)).prod * quadraticVandermonde s

theorem quadraticFactorProduct_monic (s : List ℤ) : (quadraticFactorProduct s).Monic := by
  induction s with
  | nil => exact monic_one
  | cons p s ih => exact (arithmeticQuadratic_monic p).mul ih

theorem quadraticFactorProduct_resultant (p : ℤ) (s : List ℤ) :
    resultant (arithmeticQuadratic p) (quadraticFactorProduct s) =
      (s.map (fun q => q-p)).prod ^ 2 := by
  induction s with
  | nil => simp [quadraticFactorProduct]
  | cons q s ih =>
    change resultant (arithmeticQuadratic p)
      (arithmeticQuadratic q * quadraticFactorProduct s) = _
    rw [monic_resultant_mul_right (arithmeticQuadratic_monic p),
      arithmeticQuadratic_resultant, ih, List.map_cons, List.prod_cons, mul_pow]

/-- Cross-resultants contribute fourth powers, so only the factors control the sign. -/
theorem quadraticFactorProduct_discr (s : List ℤ) :
    (quadraticFactorProduct s).discr =
      (-4) ^ s.length * s.prod * quadraticVandermonde s ^ 4 := by
  induction s with
  | nil => exact Polynomial.discr_C 1
  | cons p s ih =>
    change (arithmeticQuadratic p * quadraticFactorProduct s).discr = _
    rw [discr_mul_of_monic (arithmeticQuadratic_monic p) (quadraticFactorProduct_monic s),
      arithmeticQuadratic_discr, ih, quadraticFactorProduct_resultant]
    simp only [List.length_cons, List.prod_cons, quadraticVandermonde, pow_succ]
    ring

/-- Repeated parameters are precisely the zero locus of the cross-resultants. -/
theorem quadraticVandermonde_ne_zero (s : List ℤ) :
    quadraticVandermonde s ≠ 0 ↔ s.Nodup := by
  have hrow (p : ℤ) (t : List ℤ) : (t.map (fun q => q-p)).prod ≠ 0 ↔ p ∉ t := by
    induction t with
    | nil => simp
    | cons q t ih =>
      rw [List.map_cons, List.prod_cons, mul_ne_zero_iff, ih, List.mem_cons, not_or,
        sub_ne_zero]
      exact and_congr ne_comm Iff.rfl
  induction s with
  | nil => simp [quadraticVandermonde]
  | cons p s ih =>
    simp only [quadraticVandermonde, mul_ne_zero_iff, hrow, ih, List.nodup_cons]

/-- The arithmetic polynomial, defined without a Möbius coefficient. -/
def primeQuadraticPolynomial (n : ℕ) : ℤ[X] :=
  quadraticFactorProduct (n.primeFactorsList.map (fun p : ℕ => (p : ℤ)))

/-- The integral cross-factor discriminant coordinate. -/
def primeQuadraticVandermonde (n : ℕ) : ℤ :=
  quadraticVandermonde (n.primeFactorsList.map (fun p : ℕ => (p : ℤ)))

theorem primeQuadraticPolynomial_monic (n : ℕ) : (primeQuadraticPolynomial n).Monic :=
  quadraticFactorProduct_monic _

/-- The exact discriminant, including its ramification factor. -/
theorem primeQuadraticPolynomial_discr {n : ℕ} (hn : n ≠ 0) :
    (primeQuadraticPolynomial n).discr =
      (-4) ^ n.primeFactorsList.length * n * primeQuadraticVandermonde n ^ 4 := by
  have hc (s : List ℕ) : (s.map (fun p : ℕ => (p : ℤ))).prod = (s.prod : ℤ) := by
    induction s with
    | nil => rfl
    | cons p s ih => simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul]
  rw [primeQuadraticPolynomial, quadraticFactorProduct_discr, List.length_map,
    hc, Nat.prod_primeFactorsList hn]
  rfl

/-- The cross-factor divisor vanishes exactly at nonsquarefree conductors. -/
theorem primeQuadraticVandermonde_ne_zero {n : ℕ} (hn : n ≠ 0) :
    primeQuadraticVandermonde n ≠ 0 ↔ Squarefree n := by
  rw [primeQuadraticVandermonde, quadraticVandermonde_ne_zero,
    List.nodup_map_iff (fun _ _ h => Int.ofNat_inj.mp h),
    ← Nat.squarefree_iff_nodup_primeFactorsList hn]

/-- Ramification of the orientation cover detects precisely a repeated prime factor. -/
theorem primeQuadraticPolynomial_discr_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (primeQuadraticPolynomial n).discr ≠ 0 ↔ Squarefree n := by
  rw [primeQuadraticPolynomial_discr hn]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hp : (-4 : ℤ) ^ n.primeFactorsList.length ≠ 0 :=
    pow_ne_zero _ (by decide)
  constructor
  · intro h
    apply (primeQuadraticVandermonde_ne_zero hn).mp
    intro hv
    apply h
    rw [hv, zero_pow (by decide : 4 ≠ 0), mul_zero]
  · intro hs
    exact mul_ne_zero (mul_ne_zero hp hn')
      (pow_ne_zero 4 ((primeQuadraticVandermonde_ne_zero hn).mpr hs))

/-- The actual integral discriminant has Möbius sign. -/
theorem primeQuadraticPolynomial_discr_sign {n : ℕ} (hn : n ≠ 0) :
    (primeQuadraticPolynomial n).discr.sign = moebius n := by
  by_cases hs : Squarefree n
  · have hpow (k : ℕ) : ((-4 : ℤ) ^ k).sign = (-1) ^ k := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ, Int.sign_mul, ih, Int.sign_eq_neg_one_of_neg (by decide : (-4 : ℤ) < 0),
          pow_succ]
    have hv := (primeQuadraticVandermonde_ne_zero hn).mpr hs
    have hv4 : 0 < primeQuadraticVandermonde n ^ 4 := by
      exact (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_pos hv
    have hn' : 0 < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [primeQuadraticPolynomial_discr hn, mul_assoc, Int.sign_mul, hpow,
      Int.sign_eq_one_of_pos (mul_pos hn' hv4), mul_one, moebius_apply_of_squarefree hs]
    rfl
  · have hd : (primeQuadraticPolynomial n).discr = 0 := by
      by_contra h
      exact hs ((primeQuadraticPolynomial_discr_ne_zero hn).mp h)
    rw [hd, Int.sign_zero, moebius_eq_zero_of_not_squarefree hs]

#print axioms quadraticFactorProduct_discr
#print axioms primeQuadraticPolynomial_discr
#print axioms primeQuadraticPolynomial_discr_ne_zero
#print axioms primeQuadraticPolynomial_discr_sign

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
