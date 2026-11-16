import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionRamification

/-!
# Ramification over geometric Hermitian points

In the actual geometric normalization, the polynomial-coordinate map is
unramified at points with nonzero radical coordinate. At every point with
zero radical coordinate its index is exactly `Q+1`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "B" => HermitianGeometricNormalization p s
local notation "η" => hermitianExtensionTraceConstant p s E

/-- The polynomial-coordinate image of a geometric Hermitian point. -/
def hermitianGeometricBaseCoordinate (P : HermitianAffinePoint p s E) : E :=
  (η : E) * P.val.2

/-- Trace normalization converts every scalar branch value to the Hermitian additive value. -/
theorem hermitianGeometricBranch_eval (b : E) :
    (kummerBranch η⁻¹ (Q - 2) 1).eval ((η : E) * b) = b ^ Q + b := by
  let y := (η : E) * b
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hbranch : y * (1 - y ^ (Q - 2 + 1)) = y - y ^ Q := by
    rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  simp only [kummerBranch, eval_mul, eval_C, eval_X, eval_pow, eval_sub, eval_one,
    pow_one, Units.val_inv_eq_inv_val]
  change (η : E)⁻¹ * y * (1 - y ^ (Q - 2 + 1)) = _
  rw [mul_assoc, hbranch]
  change (η : E)⁻¹ * ((η : E) * b - ((η : E) * b) ^ Q) = _
  rw [mul_pow, hermitianExtensionTraceConstant_frobenius]
  calc
    _ = (η : E)⁻¹ * (η : E) * (b + b ^ Q) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, one_mul]
      ring

/-- The branch value at every geometric point is its radical coordinate to the covering degree. -/
theorem hermitianGeometricPoint_branch (P : HermitianAffinePoint p s E) :
    (kummerBranch η⁻¹ (Q - 2) 1).eval (hermitianGeometricBaseCoordinate p s P) =
      P.val.1 ^ (Q + 1) :=
  (hermitianGeometricBranch_eval p s P.val.2).trans P.property

/-- A nonzero radical coordinate gives ramification index one in the actual normalization. -/
theorem hermitianGeometricPoint_unramified (P : HermitianAffinePoint p s E)
    (hP : P.val.1 ≠ 0) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)})] :
    (Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)}).ramificationIdx' w.asIdeal = 1 := by
  apply squareKummerExtension_nonbranch_ramification p s E η⁻¹ (Q - 2) 1
  rw [hermitianGeometricPoint_branch]
  exact pow_ne_zero _ hP

/-- Every zero radical coordinate lies over a simple root of the branch polynomial. -/
theorem hermitianGeometricPoint_branchMultiplicity (P : HermitianAffinePoint p s E)
    (hP : P.val.1 = 0) :
    (kummerBranch η⁻¹ (Q - 2) 1).rootMultiplicity
      (hermitianGeometricBaseCoordinate p s P) = 1 := by
  let y := hermitianGeometricBaseCoordinate p s P
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hb : P.val.2 ^ Q + P.val.2 = 0 := by
    rw [P.property, hP, zero_pow (Nat.succ_ne_zero _)]
  have hy : y ^ Q = y := by
    change ((η : E) * P.val.2) ^ Q = (η : E) * P.val.2
    rw [mul_pow, hermitianExtensionTraceConstant_frobenius]
    linear_combination -(η : E) * hb
  by_cases hy0 : y = 0
  · change (kummerBranch η⁻¹ (Q - 2) 1).rootMultiplicity y = 1
    rw [hy0, kummerBranch_rootMultiplicity_origin]
  · have hcast : (p ^ (s + 1) : E) = 0 := by
      rw [CharP.cast_eq_zero E p, zero_pow (Nat.succ_ne_zero s)]
    have hi : ((Q - 2 : ℕ) : E) + 1 ≠ 0 := by
      have hs := congrArg (fun n : ℕ => (n : E))
        (show Q - 2 + 1 + 1 = Q by omega)
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hs
      rw [hcast] at hs
      intro hz
      rw [hz, zero_add] at hs
      exact one_ne_zero hs
    apply kummerBranch_rootMultiplicity_nonzero η⁻¹ (Q - 2) 1 hi y hy0
    rw [show Q - 2 + 1 = Q - 1 by omega]
    apply mul_right_cancel₀ hy0
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ Q)]
    exact hy

/-- A zero radical coordinate has the full covering ramification index. -/
theorem hermitianGeometricPoint_totallyRamified (P : HermitianAffinePoint p s E)
    (hP : P.val.1 = 0) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)})] :
    (Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)}).ramificationIdx' w.asIdeal = Q + 1 := by
  rw [squareKummerExtension_rationalPlace_ramification,
    hermitianGeometricPoint_branchMultiplicity p s P hP, Nat.gcd_one_right, Nat.div_one]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
