import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityFunctionOrders


/-!
# Pole orders of reduced radical monomials

The unique infinity valuation gives the exact order
`i+(q-1)(iR mod (Q+1))` of each reduced integral radical monomial.
The branch equation and Euclidean division remove the denominator contribution.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- The nonlinear branch factor has pole order `(Q+1)(q-1)` at infinity. -/
theorem squareKummerInfinityValuation_branchFactor :
    squareKummerInfinityValuation p s c d r
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
          (1 - X ^ (p ^ (d + 1) - 2 + 1))) =
      WithZero.exp (((p ^ (s + 1) + 1) * (p ^ (d + 1) - 1) : ℕ) : ℤ) := by
  let v := squareKummerInfinityValuation p s c d r
  let y := algebraMap (SquareConstantField p s)[X]
    (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hpow : v (y ^ (p ^ (d + 1) - 1)) =
      WithZero.exp (((p ^ (s + 1) + 1) * (p ^ (d + 1) - 1) : ℕ) : ℤ) := by
    rw [map_pow, squareKummerInfinityValuation_coordinate, ← WithZero.exp_nsmul, nsmul_eq_mul]
    congr 1
    push_cast
    ring
  rw [map_sub, map_one, map_pow, show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega]
  change v (1 - y ^ (p ^ (d + 1) - 1)) = _
  rw [v.map_sub_eq_of_lt_right, hpow]
  rw [map_one, hpow, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  exact_mod_cast Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt hq)

/-- The reduced radical monomial has pole order `i+(q-1)(iR mod (Q+1))`. -/
theorem squareKummerInfinityValuation_integralMonomial (i : ℕ) :
    squareKummerInfinityValuation p s c d r
      (kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i) =
      WithZero.exp ((i + (p ^ (d + 1) - 1) *
        (i * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1)) : ℕ) : ℤ) := by
  rw [kummerIntegralMonomial, map_div₀, map_pow, map_pow,
    squareKummerInfinityValuation_root, squareKummerInfinityValuation_branchFactor,
    ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub]
  congr 1
  let q := p ^ (d + 1)
  let N := p ^ (s + 1) + 1
  let R := kummerExponent q r
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hbranch : R * (q - 1) + 1 = q ^ r := by
    have h := kummerExponent_mul_add (q - 1) r
    rw [Nat.sub_add_cancel hq] at h
    exact h
  have hdivision := Nat.div_add_mod (i * R) N
  have hmul := congrArg (fun x : ℕ => x * (q - 1)) hdivision
  have hex : i * q ^ r = i + (q - 1) * (i * R % N) + (N * (q - 1)) * (i * R / N) := by
    nlinarith only [hmul, congrArg (fun x : ℕ => i * x) hbranch]
  have hz := congrArg (fun x : ℕ => (x : ℤ)) hex
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hz
  change (i : ℤ) * (q ^ r : ℕ) - (i * R / N : ℕ) * (N * (q - 1) : ℕ) =
    (i + (q - 1) * (i * R % N) : ℕ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  nlinarith only [hz]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
