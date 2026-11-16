import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTangentDivisors

/-!
# Torsion of actual rational Hermitian point classes

The reciprocal tangent has principal divisor `(Q+1)(P-infinity)` in
valuation-log convention. Thus every rational affine point-minus-infinity
class in the actual place-divisor quotient is killed by Q+1.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "B" => SquareKummerNormalization p s η⁻¹ (Q - 2) 1
local notation "HK" => HermitianAffinePoint p s K
local notation "D" => PrimePowerKummerPlaceDivisor p s 0 1 η⁻¹
local notation "C" => PrimePowerKummerPlaceDivisorClass p s 0 1 η⁻¹
local notation "Prin" => primePowerKummerPrincipalDivisors p s 0 1 η⁻¹

/-- The actual rational point-minus-infinity divisor. -/
def hermitianPointInfinityDivisor (P : HK) : D :=
  (Finsupp.single (hermitianPointHeightOne p s P) 1, -1)

/-- Multiplication by Q+1 makes every rational point-minus-infinity divisor principal. -/
theorem hermitianPointInfinityDivisor_nsmul_mem (P : HK) :
    (Q + 1) • hermitianPointInfinityDivisor p s P ∈ Prin := by
  classical
  have hp := primePowerKummerFunctionDivisor_mem p s 0 1 η⁻¹
    (hermitianTangentFunction p s P) (hermitianTangentFunction_ne_zero p s P)
  rw [hermitianTangent_functionDivisor p s P] at hp
  have he : (Q + 1) • hermitianPointInfinityDivisor p s P =
      -(Finsupp.single (hermitianPointHeightOne p s P) (-((Q + 1 : ℕ) : ℤ)),
        ((Q + 1 : ℕ) : ℤ)) := by
    apply Prod.ext
    · change ((Q + 1) • Finsupp.single (hermitianPointHeightOne p s P) (1 : ℤ) :
        HeightOneSpectrum B →₀ ℤ) =
          -Finsupp.single (hermitianPointHeightOne p s P) (-((Q + 1 : ℕ) : ℤ))
      apply Finsupp.ext
      intro w
      change (Q + 1) • (Finsupp.single (hermitianPointHeightOne p s P) (1 : ℤ)) w =
        -(Finsupp.single (hermitianPointHeightOne p s P) (-((Q + 1 : ℕ) : ℤ))) w
      by_cases hw : w = hermitianPointHeightOne p s P
      · subst w
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
        simp only [nsmul_eq_mul, mul_one, neg_neg]
      · rw [Finsupp.single_eq_of_ne hw, Finsupp.single_eq_of_ne hw]
        simp only [nsmul_zero, neg_zero]
    · change (Q + 1) • (-1 : ℤ) = -((Q + 1 : ℕ) : ℤ)
      rw [nsmul_eq_mul, mul_neg_one]
  rw [he]
  exact (primePowerKummerPrincipalDivisors p s 0 1 η⁻¹).neg_mem hp

/-- The class of an actual rational affine point minus infinity. -/
def hermitianPointInfinityClass (P : HK) : C :=
  QuotientAddGroup.mk' Prin (hermitianPointInfinityDivisor p s P)

/-- The actual rational point-minus-infinity class is killed by Q+1. -/
theorem hermitianPointInfinityClass_nsmul (P : HK) :
    (Q + 1) • hermitianPointInfinityClass p s P = 0 := by
  rw [hermitianPointInfinityClass, ← map_nsmul]
  change (((Q + 1) • hermitianPointInfinityDivisor p s P : D) : C) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact hermitianPointInfinityDivisor_nsmul_mem p s P

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
