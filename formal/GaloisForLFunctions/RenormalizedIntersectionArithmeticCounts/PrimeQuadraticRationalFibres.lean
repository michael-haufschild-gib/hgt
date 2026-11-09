import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeQuadraticDiscriminant
import GaloisForLFunctions.HTGeometry.SquarefreeNotSquareInFractionField
import Mathlib.Data.Set.Card

/-!
# Rational fibres of the prime-quadratic orientation cover

The real orientation defect does not survive passage to rational points.
At a squarefree conductor greater than one, a rational point would make
that conductor a rational square. Repeated factors instead give a single
branch point. The resulting global count depends on squarefreeness alone.
-/

noncomputable section
open Polynomial Finset ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HTGeometry

/-- The integral square factor in the absolute discriminant. -/
def primeQuadraticSquareFactor (n : ℕ) : ℤ :=
  2 ^ n.primeFactorsList.length * primeQuadraticVandermonde n ^ 2

/-- Removing an explicit integral square leaves the original conductor. -/
theorem primeQuadraticPolynomial_abs_discr {n : ℕ} (hn : n ≠ 0) :
    |(primeQuadraticPolynomial n).discr| = (n : ℤ) * primeQuadraticSquareFactor n ^ 2 := by
  have he : Even (4 : ℕ) := ⟨2, rfl⟩
  have hnonneg : 0 ≤ (n : ℤ) * primeQuadraticVandermonde n ^ 4 :=
    mul_nonneg (Nat.cast_nonneg n) (he.pow_nonneg _)
  rw [primeQuadraticPolynomial_discr hn, mul_assoc, abs_mul, abs_pow,
    abs_of_nonneg hnonneg]
  rw [abs_neg, abs_of_nonneg (by decide : (0 : ℤ) ≤ 4)]
  have hp : (4 : ℤ) ^ n.primeFactorsList.length =
      (2 ^ n.primeFactorsList.length) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  rw [hp, primeQuadraticSquareFactor]
  ring

/-- The square factor is nonzero precisely on the proper squarefree part of the family. -/
theorem primeQuadraticSquareFactor_ne_zero {n : ℕ} (hs : Squarefree n) :
    primeQuadraticSquareFactor n ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0))
    (pow_ne_zero _ ((primeQuadraticVandermonde_ne_zero hs.ne_zero).mpr hs))

/-- A nontrivial squarefree conductor admits no rational orientation. -/
theorem primeQuadratic_no_rational_root {n : ℕ} (hs : Squarefree n) (hn : n ≠ 1)
    (y : ℚ) : y ^ 2 ≠ ((primeQuadraticPolynomial n).discr : ℚ) := by
  intro hy
  have hn' : 1 < n := by have := hs.ne_zero; omega
  have hsf : Squarefree (n : ℤ) := Int.squarefree_natCast.mpr hs
  have hnu : ¬ IsUnit (n : ℤ) := by
    rw [Int.isUnit_iff]
    push Not
    constructor <;> omega
  apply not_isSquare_algebraMap_of_squarefree (K := ℚ) hsf hnu
  have hfactor : (primeQuadraticSquareFactor n : ℚ) ≠ 0 := by
    exact_mod_cast primeQuadraticSquareFactor_ne_zero hs
  have habs : y ^ 2 = (n : ℚ) * (primeQuadraticSquareFactor n : ℚ) ^ 2 := by
    calc
      y ^ 2 = |((primeQuadraticPolynomial n).discr : ℚ)| := by
        rw [← hy, abs_of_nonneg (sq_nonneg y)]
      _ = (|(primeQuadraticPolynomial n).discr| : ℤ) := by rw [Int.cast_abs]
      _ = (n : ℚ) * (primeQuadraticSquareFactor n : ℚ) ^ 2 := by
        exact_mod_cast primeQuadraticPolynomial_abs_discr hs.ne_zero
  refine ⟨y / (primeQuadraticSquareFactor n : ℚ), ?_⟩
  change (n : ℚ) = (y / (primeQuadraticSquareFactor n : ℚ)) *
    (y / (primeQuadraticSquareFactor n : ℚ))
  rw [← pow_two, div_pow]
  exact (eq_div_iff (pow_ne_zero 2 hfactor)).mpr habs.symm

/-- Actual rational points of the same integral equation used at the real place. -/
def primeQuadraticRationalRootSet (n : ℕ) : Set ℚ :=
  {y | y ^ 2 = ((primeQuadraticPolynomial n).discr : ℚ)}

/-- The full rational fibre, including the conductor-one and repeated-factor branches. -/
theorem primeQuadraticRationalRootSet_eq {n : ℕ} (hn : n ≠ 0) :
    primeQuadraticRationalRootSet n =
      if n = 1 then {1, -1} else if Squarefree n then ∅ else {0} := by
  by_cases h1 : n = 1
  · subst n
    have hd : (primeQuadraticPolynomial 1).discr = 1 := by
      simp only [primeQuadraticPolynomial, quadraticFactorProduct,
        Nat.primeFactorsList_one, List.map_nil, List.prod_nil]
      exact Polynomial.discr_C 1
    rw [if_pos rfl]
    ext y
    simp only [primeQuadraticRationalRootSet, hd, Int.cast_one,
      Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    simpa only [one_pow] using (sq_eq_sq_iff_eq_or_eq_neg (a := y) (b := (1 : ℚ)))
  · rw [if_neg h1]
    by_cases hs : Squarefree n
    · rw [if_pos hs]
      ext y
      simp only [primeQuadraticRationalRootSet, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      exact primeQuadratic_no_rational_root hs h1 y
    · rw [if_neg hs]
      have hd : (primeQuadraticPolynomial n).discr = 0 := by
        by_contra h
        exact hs ((primeQuadraticPolynomial_discr_ne_zero hn).mp h)
      ext y
      simp [primeQuadraticRationalRootSet, hd]

theorem primeQuadraticRationalRootSet_finite {n : ℕ} (hn : n ≠ 0) :
    (primeQuadraticRationalRootSet n).Finite := by
  rw [primeQuadraticRationalRootSet_eq hn]
  split_ifs <;> simp

/-- Rational fibres retain squarefree support but discard its Möbius orientation. -/
theorem primeQuadraticRationalRootSet_card {n : ℕ} (hn : n ≠ 0) :
    Nat.card (primeQuadraticRationalRootSet n) =
      if n = 1 then 2 else if Squarefree n then 0 else 1 := by
  rw [Nat.card_coe_set_eq, primeQuadraticRationalRootSet_eq hn]
  split_ifs
  · exact Set.ncard_pair (by norm_num : (1 : ℚ) ≠ -1)
  · exact Set.ncard_empty ℚ
  · exact Set.ncard_singleton 0

/-- Total number of rational points in the positive conductor window. -/
def primeQuadraticRationalCount (N : ℕ) : ℕ :=
  ∑ n ∈ Icc 1 N, Nat.card (primeQuadraticRationalRootSet n)

/-- The rational count has a squarefree-support defect, not a signed Möbius defect. -/
theorem primeQuadraticRationalCount_eq (N : ℕ) (hN : 1 ≤ N) :
    (primeQuadraticRationalCount N : ℤ) =
      N + 2 - ((Icc 1 N).filter Squarefree).card := by
  classical
  have hmem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (Nat.card (primeQuadraticRationalRootSet n) : ℤ) =
        1 - (if Squarefree n then 1 else 0) + (if n = 1 then 2 else 0) := by
    rw [primeQuadraticRationalRootSet_card (by have := (mem_Icc.mp hn).1; omega)]
    by_cases h1 : n = 1
    · subst n; simp
    · by_cases hs : Squarefree n <;> simp [h1, hs]
  simp only [primeQuadraticRationalCount, Nat.cast_sum]
  rw [sum_congr rfl hpoint, sum_add_distrib, sum_sub_distrib,
    sum_ite_eq', if_pos hmem, ← sum_filter Squarefree (fun _ => (1 : ℤ))]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
  ring

#print axioms primeQuadraticPolynomial_abs_discr
#print axioms primeQuadratic_no_rational_root
#print axioms primeQuadraticRationalRootSet_eq
#print axioms primeQuadraticRationalRootSet_finite
#print axioms primeQuadraticRationalRootSet_card
#print axioms primeQuadraticRationalCount_eq

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
