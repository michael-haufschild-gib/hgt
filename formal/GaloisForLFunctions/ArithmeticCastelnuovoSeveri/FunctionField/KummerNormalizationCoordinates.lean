import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralCharacterComponents
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPowerFreeDivisors

/-!
# Polynomial coordinates in the Kummer normalization

Character projectors isolate each reduced radical component of an
integral element. Raising that component to the covering degree gives
a reduced branch divisor times a power of its rational coefficient.
No denominator can survive, so the coefficient is a polynomial.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ) (R : ℕ)

/-- Every reduced radical basis coordinate of an integral element is a polynomial. -/
theorem squareKummer_integral_basis_coordinate
    (x : SquareKummerField p s c (p ^ (d + 1) - 2) R)
    (hx : IsIntegral (SquareConstantField p s)[X] x)
    (i : Fin (p ^ (s + 1) + 1)) :
    (kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))).repr x i ∈
      (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])).range := by
  let K := SquareConstantField p s
  let A := K[X]
  let F := FractionRing A
  let L := SquareKummerField p s c (p ^ (d + 1) - 2) R
  let N := p ^ (s + 1) + 1
  let B := kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))
  let a := B.repr x i
  let f : A := C ((c : K) ^ i.val) * X ^ i.val *
    (1 - X ^ (p ^ (d + 1) - 2 + 1)) ^ (i.val * R % N)
  have hcomp : IsIntegral A (a • B i) :=
    squareKummer_integral_character_component p s c (p ^ (d + 1) - 2) R x hx i
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
  apply squareKummer_reducedBranchPower_no_denominator p s d (c ^ i.val)
    N i.val (i.val * R % N) i.isLt (Nat.mod_lt _ (Nat.succ_pos _)) a
  simpa only [f, Units.val_pow_eq_pow_val] using hmem

/-- The integral closure consists exactly of polynomial combinations of the reduced radical basis. -/
theorem squareKummer_integral_iff_basis_coordinates
    (x : SquareKummerField p s c (p ^ (d + 1) - 2) R) :
    IsIntegral (SquareConstantField p s)[X] x ↔
      ∀ i : Fin (p ^ (s + 1) + 1),
        (kummerIntegralMonomialBasis c (p ^ (d + 1) - 2) R (p ^ (s + 1))).repr x i ∈
          (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])).range := by
  constructor
  · exact fun hx i => squareKummer_integral_basis_coordinate p s d c R x hx i
  · intro h
    classical
    let K := SquareConstantField p s
    let A := K[X]
    let F := FractionRing A
    let L := SquareKummerField p s c (p ^ (d + 1) - 2) R
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
