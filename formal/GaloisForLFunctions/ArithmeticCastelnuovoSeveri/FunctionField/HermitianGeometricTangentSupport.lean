import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricTangents
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianFrobeniusTangents

/-!
# Geometric contacts of a Hermitian tangent

At the normalized valuation of any geometric point, a tangent is a unit
unless the point is its defining point or its square-Frobenius image.
The second contact has order one when the two points are distinct.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "V" => hermitianGeometricPointValuation p s
local notation "φ" => algebraMap E H

private theorem radical_small (U : HermitianAffinePoint p s E) :
    V U (z - φ U.val.1) < 1 := by
  rw [hermitianGeometricPointValuation_radical_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- Subtracting a constant different from the radical residue gives a unit. -/
theorem hermitianGeometricPointValuation_radical_sub_of_ne
    (U : HermitianAffinePoint p s E) (a : E) (ha : U.val.1 ≠ a) :
    V U (z - φ a) = 1 := by
  have hc := hermitianGeometricPointValuation_constant p s U (U.val.1 - a)
    (sub_ne_zero.mpr ha)
  have hid : z - φ a = (z - φ U.val.1) + φ (U.val.1 - a) := by
    rw [map_sub]
    ring
  rw [hid]
  exact ((V U).map_add_eq_of_lt_right (hc.symm ▸ radical_small p s U)).trans hc

private theorem tangent_error_small (P U : HermitianAffinePoint p s E) :
    V U ((u - φ U.val.2) - φ (P.val.1 ^ Q) * (z - φ U.val.1)) < 1 := by
  have hs : V U (φ (P.val.1 ^ Q) * (z - φ U.val.1)) < 1 := by
    by_cases h : P.val.1 ^ Q = 0
    · rw [h, map_zero, zero_mul, map_zero]
      exact zero_lt_one
    · rw [map_mul, hermitianGeometricPointValuation_constant p s U _ h, one_mul]
      exact radical_small p s U
  exact (V U).map_sub_lt (hermitianGeometricPointValuation_additive_sub_lt_one p s U) hs

private theorem tangent_residue_decomposition (P U : HermitianAffinePoint p s E) :
    hermitianGeometricTangentFunction p s P =
      ((u - φ U.val.2) - φ (P.val.1 ^ Q) * (z - φ U.val.1)) +
        φ (U.val.2 - (hermitianTangentPolynomial p s E P).eval U.val.1) := by
  rw [hermitianGeometricTangentFunction_eq]
  simp only [hermitianTangentPolynomial, eval_add, eval_C, eval_mul, eval_sub, eval_X,
    map_sub, map_add, map_mul]
  ring

/-- The tangent is small at every geometric point incident with its line. -/
theorem hermitianGeometricPointValuation_tangent_small_of_incident
    (P U : HermitianAffinePoint p s E)
    (h : (hermitianTangentPolynomial p s E P).eval U.val.1 = U.val.2) :
    V U (hermitianGeometricTangentFunction p s P) < 1 := by
  rw [tangent_residue_decomposition p s P U, h, sub_self, map_zero, add_zero]
  exact tangent_error_small p s P U

/-- Away from the point and its Frobenius image, the actual tangent is a unit. -/
theorem hermitianGeometricPointValuation_tangent_unit
    (P U : HermitianAffinePoint p s E) (hP : U ≠ P)
    (hF : U ≠ hermitianFrobeniusPoint p s E P) :
    V U (hermitianGeometricTangentFunction p s P) = 1 := by
  have hline : (hermitianTangentPolynomial p s E P).eval U.val.1 ≠ U.val.2 := by
    intro h
    exact ((hermitianTangent_incidence_iff p s E P U).mp h).elim hP hF
  have hc := hermitianGeometricPointValuation_constant p s U
    (U.val.2 - (hermitianTangentPolynomial p s E P).eval U.val.1)
    (sub_ne_zero.mpr (Ne.symm hline))
  rw [tangent_residue_decomposition p s P U]
  exact ((V U).map_add_eq_of_lt_right (hc.symm ▸ tangent_error_small p s P U)).trans hc

/-- The distinct Frobenius contact of the tangent has normalized order one. -/
theorem hermitianGeometricPointValuation_tangent_frobenius
    (P : HermitianAffinePoint p s E)
    (hP : hermitianFrobeniusPoint p s E P ≠ P) :
    V (hermitianFrobeniusPoint p s E P) (hermitianGeometricTangentFunction p s P) =
      WithZero.exp (-1 : ℤ) := by
  let U := hermitianFrobeniusPoint p s E P
  have ha : U.val.1 ≠ P.val.1 := by
    exact fun h => hP ((hermitianFrobeniusPoint_eq_self_iff p s E P).mpr h)
  have hs := hermitianGeometricPointValuation_tangent_small_of_incident p s P U
    (hermitianTangent_eval_frobenius p s E P)
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have ht := congrArg (V U) (hermitianGeometricTangentFunction_equation p s P)
  rw [valuation_add_power_of_lt_one (V U) Q hQ _ hs, map_mul, map_pow,
    hermitianGeometricPointValuation_radical_sub_of_ne p s U P.val.1 ha,
    one_pow, one_mul] at ht
  exact ht.trans (hermitianGeometricPointValuation_radical_sub p s U)

open scoped Classical in
/-- Every geometric contact is accounted for by `Q` copies of the point and one Frobenius copy. -/
theorem hermitianGeometricPointValuation_tangent_all
    (P U : HermitianAffinePoint p s E) :
    V U (hermitianGeometricTangentFunction p s P) =
      WithZero.exp (-(((if U = P then Q else 0) +
        (if U = hermitianFrobeniusPoint p s E P then 1 else 0) : ℕ) : ℤ)) := by
  classical
  by_cases hUP : U = P
  · subst U
    by_cases hF : hermitianFrobeniusPoint p s E P = P
    · have hfix := (hermitianFrobeniusPoint_eq_self_iff p s E P).mp hF
      simpa only [if_pos rfl, if_pos hF.symm, if_pos hfix, if_pos True.intro] using
        hermitianGeometricPointValuation_tangent p s P
    · have hfix : P.val.1 ^ (Q * Q) ≠ P.val.1 :=
        fun h => hF ((hermitianFrobeniusPoint_eq_self_iff p s E P).mpr h)
      simpa only [if_pos rfl, if_neg (Ne.symm hF), if_neg hfix, if_pos True.intro,
        Nat.add_zero] using
        hermitianGeometricPointValuation_tangent p s P
  · by_cases hUF : U = hermitianFrobeniusPoint p s E P
    · subst U
      simpa only [if_neg hUP, if_pos rfl, if_pos True.intro, Nat.zero_add, Nat.cast_one] using
        hermitianGeometricPointValuation_tangent_frobenius p s P hUP
    · simpa only [if_neg hUP, if_neg hUF, Nat.zero_add, Nat.cast_zero,
        neg_zero, WithZero.exp_zero] using
        hermitianGeometricPointValuation_tangent_unit p s P U hUP hUF

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
