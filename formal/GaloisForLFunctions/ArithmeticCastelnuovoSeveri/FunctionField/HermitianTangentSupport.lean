import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginIntrinsicCharacterization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTangentPlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianInfinityAction

/-!
# Complete intrinsic support of a rational Hermitian tangent

Translation carries a tangent to the additive coordinate. The unique
zero-place characterization of that coordinate therefore identifies the
tangent's sole zero among all constant-field places. Integrality on the
finite normalization and its positive infinity pole order identify its
sole pole, without restricting to rational places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => HermitianKummerField p s
local notation "B" => SquareKummerNormalization p s η⁻¹ (Q - 2) 1
local notation "u" => hermitianKummerAdditiveCoordinate p s
local notation "v" => hermitianKummerRadicalCoordinate p s
local notation "y" => algebraMap K[X] H X
local notation "φ" => algebraMap K H
local notation "HK" => HermitianAffinePoint p s K

/-- The actual origin is the only constant-field place where the additive coordinate vanishes. -/
theorem hermitianOriginConstantPlace_iff_additive_inverse_notMem (W : ConstantFieldPlaces K H) :
    W = (hermitianOriginRationalPlace p s).val ↔ u⁻¹ ∉ W.val := by
  have hi : y⁻¹ = φ ((η : K)⁻¹) * u⁻¹ := by
    rw [← hermitianKummerAdditiveCoordinate_recover p s, mul_inv_rev, map_inv₀, mul_comm]
  calc
    W = (hermitianOriginRationalPlace p s).val ↔ y⁻¹ ∉ W.val :=
      squareKummerConstantPlace_origin_iff_inverse_notMem p s η⁻¹ s 1 W
    _ ↔ u⁻¹ ∉ W.val := by
      rw [hi, constantFieldPlace_constant_mul_mem_iff W ((η : K)⁻¹)
        (inv_ne_zero (kummerTraceConstant p s).ne_zero)]

/-- A rational tangent is a nonzero element of the actual Hermitian function field. -/
theorem hermitianTangentFunction_ne_zero (P : HK) : hermitianTangentFunction p s P ≠ 0 := by
  intro h
  have he := hermitianPointValuation_tangent p s P
  rw [h, map_zero] at he
  exact WithZero.exp_ne_zero he.symm

/-- The tangent at a rational point vanishes at no other constant-field place. -/
theorem hermitianPointConstantPlace_iff_tangent_inverse_notMem
    (P : HK) (W : ConstantFieldPlaces K H) :
    W = (hermitianPointRationalPlace p s P).val ↔ (hermitianTangentFunction p s P)⁻¹ ∉ W.val := by
  let e := hermitianTranslationFieldAut p s P
  have he : e.symm u = hermitianTangentFunction p s P := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hermitianTranslationFieldHom_tangent p s P).symm
  have h0 : constantFieldPlaceEquiv e W = (hermitianOriginRationalPlace p s).val ↔
      (hermitianTangentFunction p s P)⁻¹ ∉ W.val := by
    rw [hermitianOriginConstantPlace_iff_additive_inverse_notMem]
    change e.symm u⁻¹ ∉ W.val ↔ _
    rw [map_inv₀, he]
  have hi : constantFieldPlaceEquiv e (hermitianPointRationalPlace p s P).val =
      (hermitianOriginRationalPlace p s).val :=
    (constantFieldPlaceEquiv e).apply_symm_apply _
  constructor
  · intro hW
    apply h0.mp
    rw [hW, hi]
  · intro hW
    apply (constantFieldPlaceEquiv e).injective
    exact (h0.mpr hW).trans hi.symm

/-- Rational tangent functions are integral at every finite normalization place. -/
theorem hermitianFinitePlace_tangent_mem (P : HK) (w : HeightOneSpectrum B) :
    hermitianTangentFunction p s P ∈ (squareKummerFiniteConstantPlace p s η⁻¹ s 1 w).val := by
  let W := squareKummerFiniteConstantPlace p s η⁻¹ s 1 w
  have hy : y ∈ W.val := by
    rw [IsScalarTower.algebraMap_apply K[X] B H]
    exact algebraMap_mem_valuationSubringAtPlace H w (algebraMap K[X] B X)
  have hu : u ∈ W.val := by
    rw [hermitianKummerAdditiveCoordinate]
    exact mul_mem (W.property.2 ((η : K)⁻¹)) hy
  change u - φ P.val.2 - (φ P.val.1) ^ Q * (v - φ P.val.1) ∈ W.val
  exact sub_mem (sub_mem hu (W.property.2 P.val.2))
    (mul_mem (pow_mem (W.property.2 P.val.1) Q)
      (sub_mem (hermitianFinitePlace_radical_mem p s w) (W.property.2 P.val.1)))

/-- The actual infinity place is the only pole of every rational tangent. -/
theorem hermitianInfinityConstantPlace_iff_tangent_notMem
    (P : HK) (W : ConstantFieldPlaces K H) :
    W = (hermitianInfinityRationalPlace p s).val ↔ hermitianTangentFunction p s P ∉ W.val := by
  constructor
  · rintro rfl h
    change hermitianInfinityValuation p s (hermitianTangentFunction p s P) ≤ 1 at h
    rw [hermitianInfinityValuation_tangent, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    have hpos : (0 : ℤ) < ((Q + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos Q
    omega
  · intro h
    rcases squareKummer_constantPlace_cases p s η⁻¹ s 1 W with ⟨w, hw⟩ | hw
    · exfalso
      apply h
      rw [← hw]
      exact hermitianFinitePlace_tangent_mem p s P w
    · exact hw.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
