import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricAffineNormalization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialGeometricResidues

/-!
# Coordinates of geometric finite places

Every finite prime of the geometric Hermitian normalization has a residue
point on the affine curve. Polynomial radical expansions show that its
two coordinate residues determine its residue homomorphism, hence its prime.
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

/-- The additive Hermitian coordinate as an element of the actual affine normalization. -/
def hermitianGeometricIntegralAdditive : B :=
  algebraMap E B ((η : E)⁻¹) * algebraMap E[X] B X

/-- The radical Hermitian coordinate as an element of the actual affine normalization. -/
def hermitianGeometricIntegralRadical : B :=
  squareKummerExtensionIntegralRoot p s E η⁻¹ (Q - 2) 1

local notation "uB" => hermitianGeometricIntegralAdditive p s
local notation "zB" => hermitianGeometricIntegralRadical p s

/-- The integral additive coordinate maps to the named function-field coordinate. -/
theorem hermitianGeometricIntegralAdditive_coe :
    algebraMap B H uB = hermitianExtensionAdditiveCoordinate p s E := by
  rw [hermitianGeometricIntegralAdditive, map_mul,
    ← IsScalarTower.algebraMap_apply E B H, ← IsScalarTower.algebraMap_apply E[X] B H]
  rfl

/-- The integral radical maps to the named function-field coordinate. -/
theorem hermitianGeometricIntegralRadical_coe :
    algebraMap B H zB = hermitianExtensionRadicalCoordinate p s E := rfl

/-- The original polynomial parameter is the trace unit times the integral additive coordinate. -/
theorem hermitianGeometricIntegralAdditive_recover :
    algebraMap E B (η : E) * uB = algebraMap E[X] B X := by
  rw [hermitianGeometricIntegralAdditive, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, map_one, one_mul]

/-- The two integral coordinates satisfy the Hermitian equation in the normalization itself. -/
theorem hermitianGeometricIntegral_equation : uB ^ Q + uB = zB ^ (Q + 1) := by
  apply Subtype.ext
  change (algebraMap B H uB) ^ Q + algebraMap B H uB = (algebraMap B H zB) ^ (Q + 1)
  rw [hermitianGeometricIntegralAdditive_coe, hermitianGeometricIntegralRadical_coe]
  exact (hermitianExtensionField_equation p s E).symm

/-- Polynomial radical expansions hold inside the normalization, not just its fraction field. -/
theorem hermitianGeometricNormalization_power_expansion (b : B) :
    ∃ a : Fin (Q + 1) → E[X], b = ∑ i, algebraMap E[X] B (a i) * zB ^ i.val := by
  obtain ⟨a, ha⟩ := hermitianGeometric_integral_power_expansion p s b.val b.property
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change b.val = algebraMap B H (∑ i, algebraMap E[X] B (a i) * zB ^ i.val)
  rw [map_sum]
  simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply E[X] B H,
    hermitianGeometricIntegralRadical_coe]
  exact ha

/-- A homomorphism from the geometric normalization is determined by its two coordinate images. -/
theorem hermitianGeometricNormalization_algHom_ext
    {L : Type*} [CommRing L] [Algebra E L] (f g : B →ₐ[E] L)
    (hu : f uB = g uB) (hz : f zB = g zB) : f = g := by
  have hy : f (algebraMap E[X] B X) = g (algebraMap E[X] B X) := by
    rw [← hermitianGeometricIntegralAdditive_recover p s, map_mul, map_mul,
      f.commutes, g.commutes, hu]
  let fp : E[X] →+* L := f.toRingHom.comp (algebraMap E[X] B)
  let gp : E[X] →+* L := g.toRingHom.comp (algebraMap E[X] B)
  have hp : fp = gp := by
    apply Polynomial.ringHom_ext
    · intro c
      change f (algebraMap E[X] B (C c)) = g (algebraMap E[X] B (C c))
      have hc : algebraMap E[X] B (C c) = algebraMap E B c :=
        (IsScalarTower.algebraMap_apply E E[X] B c).symm
      rw [hc, f.commutes, g.commutes]
    · exact hy
  apply AlgHom.ext
  intro b
  obtain ⟨a, ha⟩ := hermitianGeometricNormalization_power_expansion p s b
  rw [ha, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, map_pow, map_pow, hz]
  exact congrArg (fun v : L => v * g zB ^ i.val)
    (congrArg (fun k : E[X] →+* L => k (a i)) hp)

/-- A finite normalization prime gives an actual geometric affine point by its two residues. -/
def hermitianGeometricClosedPoint (w : HeightOneSpectrum B) : HermitianAffinePoint p s E :=
  ⟨(polynomialGeometricResidue E B w zB, polynomialGeometricResidue E B w uB), by
    simpa only [map_add, map_pow] using
      congrArg (polynomialGeometricResidue E B w) (hermitianGeometricIntegral_equation p s)⟩

/-- Two finite normalization primes with the same geometric coordinates are equal. -/
theorem hermitianGeometricClosedPoint_injective :
    Function.Injective (hermitianGeometricClosedPoint p s) := by
  intro v w h
  have hz : polynomialGeometricResidue E B v zB = polynomialGeometricResidue E B w zB :=
    congrArg (fun P : HermitianAffinePoint p s E => P.val.1) h
  have hu : polynomialGeometricResidue E B v uB = polynomialGeometricResidue E B w uB :=
    congrArg (fun P : HermitianAffinePoint p s E => P.val.2) h
  have he := hermitianGeometricNormalization_algHom_ext p s
    (polynomialGeometricResidue E B v) (polynomialGeometricResidue E B w) hu hz
  have hi : v.asIdeal = w.asIdeal := by
    rw [← polynomialGeometricResidue_ker E B v, ← polynomialGeometricResidue_ker E B w, he]
  cases v
  cases w
  cases hi
  rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
