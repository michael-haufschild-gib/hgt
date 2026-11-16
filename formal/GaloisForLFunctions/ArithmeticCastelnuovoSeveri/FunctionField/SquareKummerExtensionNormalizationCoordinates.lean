import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionIntegralComponents
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPowerFreeDivisors

/-!
# Polynomial normalization coordinates over enlarged constants

Character averaging isolates integral reduced radical components. Their
power equations and squarefree branch factors exclude rational-function
denominators, over arbitrary extensions of the original square constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s d : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (c : Eˣ) (R : ℕ)

/-- The prime-power branch exponent remains nonzero after extending constants. -/
theorem squareKummerExtension_branchExponent_ne_zero :
    ((p ^ (d + 1) - 2 : ℕ) : E) + 1 ≠ 0 := by
  have h := (map_ne_zero (algebraMap (SquareConstantField p s) E)).mpr
    (squareConstantField_branchExponent_ne_zero p s d)
  simpa only [map_add, map_natCast, map_one] using h

/-- Reduced branch powers cannot cancel a rational denominator after extension of constants. -/
theorem squareKummerExtension_reducedBranchPower_no_denominator
    (N i j : ℕ) (hi : i < N) (hj : j < N)
    (x : FractionRing E[X])
    (hx : x ^ N * algebraMap E[X] (FractionRing E[X])
      (C (c : E) * X ^ i * (1 - X ^ (p ^ (d + 1) - 2 + 1)) ^ j) ∈
        (algebraMap E[X] (FractionRing E[X])).range) :
    x ∈ (algebraMap E[X] (FractionRing E[X])).range :=
  polynomial_reducedBranchPower_no_denominator c _
    (squareKummerExtension_branchExponent_ne_zero p s d E) N i j hi hj x hx

/-- Every reduced radical basis coordinate of an integral element is a polynomial. -/
theorem squareKummerExtension_integral_basis_coordinate
    (x : SquareKummerExtensionField p s E c (p ^ (d + 1) - 2) R)
    (hx : IsIntegral E[X] x)
    (i : Fin (p ^ (s + 1) + 1)) :
    (kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))).repr x i ∈
      (algebraMap E[X] (FractionRing E[X])).range := by
  let K := E
  let A := K[X]
  let F := FractionRing A
  let L := SquareKummerExtensionField p s E c (p ^ (d + 1) - 2) R
  let N := p ^ (s + 1) + 1
  let B := kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))
  let a := B.repr x i
  let f : A := C ((c : K) ^ i.val) * X ^ i.val *
    (1 - X ^ (p ^ (d + 1) - 2 + 1)) ^ (i.val * R % N)
  have hcomp : IsIntegral A (a • B i) :=
    squareKummerExtension_integral_character_component p s E c (p ^ (d + 1) - 2) R x hx i
  have hpow : (a • B i) ^ N = algebraMap F L (a ^ N * algebraMap A F f) := by
    rw [Algebra.smul_def, mul_pow, kummerIntegralMonomialBasis_apply,
      kummerIntegralMonomial_pow]
    change algebraMap F L a ^ N * algebraMap A L f =
      algebraMap F L (a ^ N * algebraMap A F f)
    rw [map_mul (algebraMap F L) (a ^ N) (algebraMap A F f),
      map_pow (algebraMap F L) a N, ← IsScalarTower.algebraMap_apply A F L]
  have hint : IsIntegral A (a ^ N * algebraMap A F f) := by
    apply (isIntegral_algebraMap_iff (algebraMap F L).injective).mp
    rw [← hpow]
    exact hcomp.pow N
  have hmem : a ^ N * algebraMap A F f ∈ (algebraMap A F).range :=
    IsIntegrallyClosedIn.isIntegral_iff.mp hint
  apply squareKummerExtension_reducedBranchPower_no_denominator p s d E (c ^ i.val)
    N i.val (i.val * R % N) i.isLt (Nat.mod_lt _ (Nat.succ_pos _)) a
  simpa only [f, Units.val_pow_eq_pow_val] using hmem

/-- The integral closure consists exactly of polynomial combinations of the reduced radical basis. -/
theorem squareKummerExtension_integral_iff_basis_coordinates
    (x : SquareKummerExtensionField p s E c (p ^ (d + 1) - 2) R) :
    IsIntegral E[X] x ↔
      ∀ i : Fin (p ^ (s + 1) + 1),
        (kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))).repr x i ∈
          (algebraMap E[X] (FractionRing E[X])).range := by
  constructor
  · exact fun hx i => squareKummerExtension_integral_basis_coordinate p s d E c R x hx i
  · intro h
    classical
    let K := E
    let A := K[X]
    let F := FractionRing A
    let L := SquareKummerExtensionField p s E c (p ^ (d + 1) - 2) R
    let B := kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))
    have hc (i : Fin (p ^ (s + 1) + 1)) : IsIntegral A (B.repr x i • B i) := by
      obtain ⟨a, ha⟩ := h i
      rw [Algebra.smul_def]
      change IsIntegral A (algebraMap F L (B.repr x i) * B i)
      rw [← ha, ← IsScalarTower.algebraMap_apply A F L]
      exact (isIntegral_algebraMap (x := a)).mul
        (kummerIntegralMonomialBasis_integral c (p ^ (d + 1) - 2) R (p ^ (s + 1)) i)
    rw [← B.sum_repr x]
    exact show (∑ i, B.repr x i • B i) ∈ integralClosure A L from sum_mem fun i _ => hc i

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
