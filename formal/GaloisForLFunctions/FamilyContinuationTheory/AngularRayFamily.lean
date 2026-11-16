import GaloisForLFunctions.FamilyContinuationTheory.AngularLFunctionBounds
import GaloisForLFunctions.FamilyContinuationTheory.AngularPlainIdealSums
import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation
import GaloisForLFunctions.HeckeLFunctions.ResidueCharactersTrivialOnUnitsAreHeckeCharacters

/-! # Ray class realization of the finite angular row family

Every unit-trivial Eisenstein residue character is an actual ray class character.
Its zero-extended ideal values coincide with the coefficients of the plain rows.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein HeckeFamily
local notation "O" => Eisenstein.O
local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- The ray modulus attached to a finite row character has no real-place component. -/
def angularRayModulus (χ : Character) : Modulus K where
  fin := χ.modulus
  fin_ne_bot := χ.modulus_ne_bot
  inf := ∅

private def angularRayResidue (χ : Character) :
    (O ⧸ (angularRayModulus χ).fin)ˣ × ((angularRayModulus χ).inf → ℤˣ) →* ℂˣ :=
  χ.residue.toUnitHom.comp (MonoidHom.fst _ _)

private theorem angularRayResidue_units (χ : Character) (u : Oˣ) :
    angularRayResidue χ (rayHom (angularRayModulus χ)
      (globalUnitPrimeTo (angularRayModulus χ) u)) = 1 := by
  apply Units.ext
  change (χ.residue.toUnitHom (reduce (angularRayModulus χ)
    (globalUnitPrimeTo (angularRayModulus χ) u)) : ℂ) = 1
  rw [reduce_globalUnit]
  exact χ.unit_trivial u

/-- Actual ray class character realizing the finite row character. -/
def angularRayCharacter (χ : Character) : HeckeCharacter (angularRayModulus χ) :=
  heckeOfResidue (angularRayModulus χ) (angularRayResidue χ) (angularRayResidue_units χ)

/-- The residue character is preserved on units and on nonunits. -/
theorem finiteHeckeWeight_angularRayCharacter (χ : Character) :
    finiteHeckeWeight (angularRayModulus χ) (angularRayCharacter χ) = χ.residue := by
  ext u
  rw [finiteHeckeWeight_unit, angularRayCharacter, finiteResidueCharacter_heckeOfResidue]
  rfl

/-- Equality on every integral ideal includes the zero extension at conductor divisors. -/
theorem idealCoeff_eq_angularRayValue (χ : Character) (I : Ideal O) :
    idealCoeff χ I = heckeValue (angularRayModulus χ) (angularRayCharacter χ) I := by
  by_cases hI : I = ⊥
  · subst I
    change idealCoeff χ 0 = _
    rw [map_zero, heckeValue_bot]
  · rw [← span_cubicIdealGenerator I, idealCoeff_span χ (cubicIdealGenerator_ne_zero I hI),
      ← integralHeckeWeight_eq_heckeValue (angularRayModulus χ) (angularRayCharacter χ)
        (cubicIdealGenerator_ne_zero I hI)]
    change χ.residue _ = finiteHeckeWeight (angularRayModulus χ) (angularRayCharacter χ) _
    rw [finiteHeckeWeight_angularRayCharacter]
    rfl

/-- The angular L-function at the original finite modulus, with the specified
additional Euler factors deleted. -/
def angularRowLFunction (χ : Character) (k : ℕ) (S : Finset (IsDedekindDomain.HeightOneSpectrum O))
    (w : ℂ) : ℂ :=
  grossenLFunction (angularRayModulus χ) (angularRayCharacter χ) k w *
    grossenDeletedFactors (angularRayModulus χ) (angularRayCharacter χ) k S w

/-- Its Euler product has exactly the coefficients of the finite angular row family. -/
theorem angularRowLFunction_eq_eulerProduct (χ : Character) {k : ℕ} (hk : 1 ≤ k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum O)) {w : ℂ} (hw : 1 < w.re) :
    angularRowLFunction χ k S w =
      ∏' v : {v : IsDedekindDomain.HeightOneSpectrum O // v ∉ S},
        (1 - idealPsiSix v.1.asIdeal ^ k * idealCoeff χ v.1.asIdeal *
          (primeNorm v.1 : ℂ) ^ (-w))⁻¹ := by
  rw [angularRowLFunction, ← grossenEulerProductModS_eq_mul_deletedFactors
    (angularRayModulus χ) (angularRayCharacter χ) hk S hw, grossenEulerProductModS]
  simp only [idealCoeff_eq_angularRayValue]

/-- Holomorphic continuation at the original modulus follows from primitive continuation
and the entire finite Euler product. -/
theorem differentiableOn_angularRowLFunction (χ : Character) {k : ℕ} (hk : 1 ≤ k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum O)) :
    DifferentiableOn ℂ (angularRowLFunction χ k S) {w : ℂ | -(3 * (k : ℝ)) < w.re} :=
  (differentiableOn_grossenLFunction (angularRayModulus χ) (angularRayCharacter χ) hk).mul
    (differentiable_grossenDeletedFactors
      (angularRayModulus χ) (angularRayCharacter χ) k S).differentiableOn

/-- Euler deletion introduces no zeros in the positive half-plane. -/
theorem angularRowLFunction_ne_zero_iff (χ : Character) (k : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum O)) {w : ℂ} (hw : 0 < w.re) :
    angularRowLFunction χ k S w ≠ 0 ↔
      grossenLFunction (angularRayModulus χ) (angularRayCharacter χ) k w ≠ 0 := by
  rw [angularRowLFunction, mul_ne_zero_iff]
  exact and_iff_left (grossenDeletedFactors_ne_zero
    (angularRayModulus χ) (angularRayCharacter χ) k S hw)

/-- Uniform height degree survives passage to every finite row character and deletion
of Euler factors. Both finite conductor and deletion costs remain explicit. -/
theorem angularRowLFunction_strip_bound :
    ∃ d : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (χ : Character) (S : Finset (IsDedekindDomain.HeightOneSpectrum O)) (w : ℂ),
      w.re ∈ Set.Icc (0 : ℝ) (11 / 10) →
        ‖angularRowLFunction χ k S w‖ ≤
          C * (Ideal.absNorm (heckeFiniteConductor (angularRayModulus χ)
            (angularRayCharacter χ)) : ℝ) ^ (3 / 5 : ℝ) *
              2 ^ Fintype.card (GrossenBadPrime (angularRayModulus χ) S) *
                (3 + |w.im|) ^ d := by
  obtain ⟨d, hb⟩ := grossenLFunction_conductor_strip_bound
  refine ⟨d, ?_⟩
  intro k hk
  obtain ⟨C, hC, hb⟩ := hb k hk
  refine ⟨C, hC, ?_⟩
  intro χ S w hw
  have hz : w ∈ HeckeStrip.closedStrip := ⟨by linarith only [hw.1], hw.2⟩
  have hL := hb (angularRayModulus χ) (angularRayCharacter χ) w hz
  have hE := norm_grossenDeletedFactors_le
    (angularRayModulus χ) (angularRayCharacter χ) k S hw.1
  rw [angularRowLFunction, norm_mul]
  calc
    _ ≤ (C * (Ideal.absNorm (heckeFiniteConductor (angularRayModulus χ)
        (angularRayCharacter χ)) : ℝ) ^ (3 / 5 : ℝ) * (3 + |w.im|) ^ d) *
          2 ^ Fintype.card (GrossenBadPrime (angularRayModulus χ) S) :=
      mul_le_mul hL hE (norm_nonneg _) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.FamilyContinuationTheory
