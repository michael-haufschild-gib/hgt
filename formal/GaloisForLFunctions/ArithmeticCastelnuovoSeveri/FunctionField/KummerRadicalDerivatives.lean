import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDifferentialKernel
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityRamification

/-!
# Frobenius-linear radical coordinates

The geometric exponent satisfies `R=1+qS`. Consequently the radical
coordinate is a Frobenius-field coefficient times `y-y^q`. Its ordinary
coordinate derivative is that coefficient, and its second derivative
vanishes. Both assertions hold inside the constructed function field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "q" => p ^ (d + 1)
local notation "Q" => p ^ (s + 1)
local notation "R" => kummerExponent q (r + 1)
local notation "S" => kummerExponent q r
local notation "L" => SquareKummerField p s c (q - 2) R
local notation "y" => algebraMap K[X] L X
local notation "z" => AdjoinRoot.root (kummerBranchFieldPolynomial c (q - 2) R Q)

private theorem exponent_succ (a t : ℕ) :
    kummerExponent a (t + 1) = a * kummerExponent a t + 1 := by
  unfold kummerExponent
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ', ← Finset.mul_sum]

/-- The Frobenius-field coefficient of the radical's affine coordinate expression. -/
def squareKummerRadicalDerivativeCoefficient : L :=
  algebraMap K L c * ((1 - y ^ (q - 1)) ^ S) ^ q / z ^ Q

/-- The radical's derivative coefficient belongs to the actual `p`th-power subfield. -/
theorem squareKummerRadicalDerivativeCoefficient_mem_frobenius :
    squareKummerRadicalDerivativeCoefficient p s c d r ∈
      SquareKummerFrobeniusField p s c (q - 2) R := by
  let P := SquareKummerFrobeniusField p s c (q - 2) R
  have hn : ((1 - y ^ (q - 1)) ^ S) ^ q ∈ P := by
    refine ⟨((1 - y ^ (q - 1)) ^ S) ^ p ^ d, ?_⟩
    exact (pow_mul (((1 - y ^ (q - 1)) ^ S)) (p ^ d) p).symm.trans
      (congrArg (fun k : ℕ => ((1 - y ^ (q - 1)) ^ S) ^ k) (pow_succ p d).symm)
  have hd : z ^ Q ∈ P := by
    refine ⟨z ^ p ^ s, ?_⟩
    exact (pow_mul z (p ^ s) p).symm.trans
      (congrArg (fun k : ℕ => z ^ k) (pow_succ p s).symm)
  exact P.div_mem (P.mul_mem (P.algebraMap_mem (c : K)) hn) hd

/-- The radical is a Frobenius-field coefficient times the first additive-coordinate difference. -/
theorem squareKummer_radical_frobenius_affine :
    z = squareKummerRadicalDerivativeCoefficient p s c d r * (y - y ^ q) := by
  let h : L := 1 - y ^ (q - 1)
  let A := squareKummerRadicalDerivativeCoefficient p s c d r
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hz : z ≠ 0 := kummerBranchField_root_ne_zero c (q - 2) R Q
  have hden : z ^ Q ≠ 0 := pow_ne_zero _ hz
  have hA : A * z ^ Q = algebraMap K L c * (h ^ S) ^ q := div_mul_cancel₀ _ hden
  have hy : y * h = y - y ^ q := by
    dsimp only [h]
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have hh : h ^ R = (h ^ S) ^ q * h := by
    calc
      h ^ R = h ^ (q * S + 1) := congrArg (fun k : ℕ => h ^ k) (exponent_succ q r)
      _ = h ^ (q * S) * h := pow_succ h (q * S)
      _ = (h ^ S) ^ q * h := congrArg (fun u : L => u * h)
        ((congrArg (fun k : ℕ => h ^ k) (Nat.mul_comm q S)).trans (pow_mul h S q))
  have hroot : z ^ (Q + 1) = algebraMap K L c * y * h ^ R := by
    rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply,
      kummerBranch, map_mul, map_mul, map_pow, map_sub, map_one, map_pow]
    rw [show q - 2 + 1 = q - 1 by omega]
    change algebraMap K[X] L (C (c : K)) * y * h ^ R = _
    rw [show algebraMap K[X] L (C (c : K)) = algebraMap K L c from
      (IsScalarTower.algebraMap_apply K K[X] L c).symm]
  change z = A * (y - y ^ q)
  apply mul_right_cancel₀ hden
  rw [← pow_succ' z Q, hroot, mul_right_comm A (y - y ^ q) (z ^ Q), hA, ← hy, hh]
  ring

/-- Differentiating the radical in the rational coordinate gives the explicit Frobenius coefficient. -/
theorem squareKummerCoordinateDerivation_root :
    squareKummerCoordinateDerivation p s c (q - 2) R z =
      squareKummerRadicalDerivativeCoefficient p s c d r := by
  let D := squareKummerCoordinateDerivation p s c (q - 2) R
  let A := squareKummerRadicalDerivativeCoefficient p s c d r
  have hA : D A = 0 :=
    (squareKummerCoordinateDerivation_eq_zero_iff p s c (q - 2) R A).mpr
      (squareKummerRadicalDerivativeCoefficient_mem_frobenius p s c d r)
  have hy : D y = 1 := by
    rw [squareKummerCoordinateDerivation_polynomial, derivative_X, map_one]
  have hyq : D (y ^ q) = 0 := by
    have he : y ^ q = (y ^ p ^ d) ^ p :=
      (congrArg (fun k : ℕ => y ^ k) (pow_succ p d)).trans (pow_mul y (p ^ d) p)
    rw [he]
    exact derivation_frobenius_power_eq_zero p D (y ^ p ^ d)
  have h := congrArg D (squareKummer_radical_frobenius_affine p s c d r)
  change D z = D (A * (y - y ^ q)) at h
  rw [D.leibniz, map_sub, hy, hyq, sub_zero, hA, smul_zero, add_zero,
    smul_eq_mul, mul_one] at h
  exact h

/-- The second coordinate derivative of the radical vanishes throughout the geometric-exponent family. -/
theorem squareKummerCoordinateDerivation_root_twice :
    squareKummerCoordinateDerivation p s c (q - 2) R
      (squareKummerCoordinateDerivation p s c (q - 2) R z) = 0 := by
  rw [squareKummerCoordinateDerivation_root, squareKummerCoordinateDerivation_eq_zero_iff]
  exact squareKummerRadicalDerivativeCoefficient_mem_frobenius p s c d r

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
