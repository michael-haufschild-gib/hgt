import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricClosedPoints
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricTangents
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationPlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.NormalizedValuationUniqueness

/-!
# All finite geometric Hermitian places

The normalized valuation constructed at an affine point contains both
coordinates and all constants. Its center on the actual normalization has
the prescribed residues. Conversely, the two residues determine a finite
prime, giving a bijection between affine points and all finite primes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "η" => hermitianExtensionTraceConstant p s E
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "V" => hermitianGeometricPointValuation p s

/-- Every constructed point valuation is the normalized valuation of an actual finite prime. -/
theorem hermitianGeometricPoint_exists_prime (P : HermitianAffinePoint p s E) :
    ∃ w : HeightOneSpectrum B, w.valuation H = V P := by
  let W := (V P).valuationSubring
  have hW : W ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hermitianGeometricPointValuation_surjective p s P (WithZero.exp (1 : ℤ))
    have hm : x ∈ W := by rw [h]; trivial
    have hv := (Valuation.mem_valuationSubring_iff (V P) x).mp hm
    rw [hx] at hv
    have hlt : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (1 : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact zero_lt_one
    exact (not_lt_of_ge hv) hlt
  have hK (a : E) : algebraMap E H a ∈ W := by
    apply (Valuation.mem_valuationSubring_iff (V P) _).mpr
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero]
      exact zero_le_one
    · rw [hermitianGeometricPointValuation_constant p s P a ha]
  have hu : u ∈ W := by
    have hd : u - algebraMap E H P.val.2 ∈ W :=
      (Valuation.mem_valuationSubring_iff (V P) _).mpr
        (le_of_lt (hermitianGeometricPointValuation_additive_sub_lt_one p s P))
    simpa only [sub_add_cancel] using W.add_mem _ _ hd (hK P.val.2)
  have hy : algebraMap E[X] H X ∈ W := by
    rw [← hermitianExtensionAdditiveCoordinate_recover p s E]
    exact W.mul_mem _ _ (hK (η : E)) hu
  obtain ⟨w, hw⟩ := polynomialNormalization_finitePlace_of_coordinate_mem W hW hK hy
  exact ⟨w, normalizedValuation_eq_of_valuationSubring_eq (w.valuation H) (V P) hw
    (w.valuation_surjective H) (hermitianGeometricPointValuation_surjective p s P)⟩

/-- The finite normalization prime at the specified geometric point. -/
def hermitianGeometricPointPrime (P : HermitianAffinePoint p s E) : HeightOneSpectrum B :=
  (hermitianGeometricPoint_exists_prime p s P).choose

/-- The prime's normalized valuation agrees exactly with the constructed point valuation. -/
theorem hermitianGeometricPointPrime_valuation (P : HermitianAffinePoint p s E) :
    (hermitianGeometricPointPrime p s P).valuation H = V P :=
  (hermitianGeometricPoint_exists_prime p s P).choose_spec

/-- Taking the coordinate residues of the point prime recovers the original point. -/
theorem hermitianGeometricClosedPoint_pointPrime (P : HermitianAffinePoint p s E) :
    hermitianGeometricClosedPoint p s (hermitianGeometricPointPrime p s P) = P := by
  let w := hermitianGeometricPointPrime p s P
  have hz : polynomialGeometricResidue E B w (hermitianGeometricIntegralRadical p s) = P.val.1 := by
    apply (polynomialGeometricResidue_eq_iff E B w _ _).mpr
    apply (w.valuation_lt_one_iff_mem (K := H) _).mp
    change w.valuation H (algebraMap B H
      (hermitianGeometricIntegralRadical p s - algebraMap E B P.val.1)) < 1
    rw [map_sub, ← IsScalarTower.algebraMap_apply E B H,
      hermitianGeometricIntegralRadical_coe, hermitianGeometricPointPrime_valuation,
      hermitianGeometricPointValuation_radical_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu : polynomialGeometricResidue E B w (hermitianGeometricIntegralAdditive p s) = P.val.2 := by
    apply (polynomialGeometricResidue_eq_iff E B w _ _).mpr
    apply (w.valuation_lt_one_iff_mem (K := H) _).mp
    change w.valuation H (algebraMap B H
      (hermitianGeometricIntegralAdditive p s - algebraMap E B P.val.2)) < 1
    rw [map_sub, ← IsScalarTower.algebraMap_apply E B H,
      hermitianGeometricIntegralAdditive_coe, hermitianGeometricPointPrime_valuation]
    exact hermitianGeometricPointValuation_additive_sub_lt_one p s P
  exact Subtype.ext (Prod.ext hz hu)

/-- Every finite prime is the point prime of its two coordinate residues. -/
theorem hermitianGeometricPointPrime_closedPoint (w : HeightOneSpectrum B) :
    hermitianGeometricPointPrime p s (hermitianGeometricClosedPoint p s w) = w :=
  hermitianGeometricClosedPoint_injective p s
    (hermitianGeometricClosedPoint_pointPrime p s (hermitianGeometricClosedPoint p s w))

/-- Finite normalization primes and geometric affine points are in bijection. -/
def hermitianGeometricFinitePointEquiv : HeightOneSpectrum B ≃ HermitianAffinePoint p s E where
  toFun := hermitianGeometricClosedPoint p s
  invFun := hermitianGeometricPointPrime p s
  left_inv := hermitianGeometricPointPrime_closedPoint p s
  right_inv := hermitianGeometricClosedPoint_pointPrime p s

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
