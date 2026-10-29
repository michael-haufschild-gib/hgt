import GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsAreInverseHeckeValues
import GaloisForLFunctions.HTGeometry.FractionalIdealElementsAreClassUnitOrbits
import GaloisForLFunctions.HTGeometry.NumberFieldTraceDualsHaveDiscriminantNorms

/-!
# Actual dual Hecke frequencies have ideal-class generators

The fractional-ideal orbit equivalence supplies generators in the actual
modulus-product trace dual. Their integral ideals are exactly the orbit
indices, so the proved Fourier identity gives their inverse Hecke values.
The discriminant norm formula retains the exact conductor and base norm.
Multiplication by the base ideal identifies all dual classes with one
fixed class shift, giving the permutation used in the global class sum.
-/

noncomputable section
open NumberField
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb0 : b ≠ ⊥)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "Jdual" => FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)

/-- The actual trace-dual ideal as an invertible fractional ideal. -/
def heckeDualIdealUnit : FIˣ := Units.mk0 Jdual (heckeDualProductIdeal_ne_zero 𝔪 hb0)

/-- Integral ideals indexing the actual nonzero dual-theta unit orbits. -/
abbrev heckeDualClassIdeals := fractionalInverseClassIntegralIdeals (heckeDualIdealUnit 𝔪 hb0)

/-- The selected generator is an actual frequency in the modulus-product trace dual. -/
def heckeDualClassFrequency (I : heckeDualClassIdeals 𝔪 hb0) : Jdual :=
  ⟨fractionalClassGenerator (heckeDualIdealUnit 𝔪 hb0) I,
    fractionalClassGenerator_mem (heckeDualIdealUnit 𝔪 hb0) I⟩

theorem heckeDualClassFrequency_ne_zero (I : heckeDualClassIdeals 𝔪 hb0) :
    (heckeDualClassFrequency 𝔪 hb0 I : K) ≠ 0 :=
  fractionalClassGenerator_ne_zero (heckeDualIdealUnit 𝔪 hb0) I

/-- The orbit index agrees with the integral ideal constructed from the actual frequency. -/
theorem heckeDualFrequencyIdeal_classFrequency (I : heckeDualClassIdeals 𝔪 hb0) :
    heckeDualFrequencyIdeal 𝔪 hb0 (heckeDualClassFrequency 𝔪 hb0 I) = (I.1 : Ideal (𝓞 K)) := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change (heckeDualFrequencyIdeal 𝔪 hb0 (heckeDualClassFrequency 𝔪 hb0 I) : FI) =
    ((I.1 : Ideal (𝓞 K)) : FI)
  apply mul_right_cancel₀ (heckeDualProductIdeal_ne_zero 𝔪 hb0)
  rw [heckeDualFrequencyIdeal_mul_dual]
  exact span_fractionalClassGenerator (heckeDualIdealUnit 𝔪 hb0) I

/-- The trace dual has the exact reciprocal discriminant, conductor, and base-ideal norm. -/
theorem absNorm_heckeDualProductIdeal :
    FractionalIdeal.absNorm Jdual =
      (((NumberField.discr K).natAbs : ℚ) * (Ideal.absNorm 𝔪.fin : ℚ) *
        (Ideal.absNorm b : ℚ))⁻¹ := by
  rw [absNorm_numberField_traceDual, FractionalIdeal.coeIdeal_absNorm, map_mul, Nat.cast_mul,
    mul_assoc]

/-- The selected frequency norm retains the exact denominator for the completed equation. -/
theorem norm_heckeDualClassFrequency (I : heckeDualClassIdeals 𝔪 hb0) :
    |Algebra.norm ℚ (heckeDualClassFrequency 𝔪 hb0 I : K)| =
      (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℚ) *
        (((NumberField.discr K).natAbs : ℚ) * (Ideal.absNorm 𝔪.fin : ℚ) *
          (Ideal.absNorm b : ℚ))⁻¹ := by
  change |Algebra.norm ℚ (fractionalClassGenerator (heckeDualIdealUnit 𝔪 hb0) I)| = _
  rw [norm_fractionalClassGenerator]
  exact congrArg ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℚ) * ·)
    (absNorm_heckeDualProductIdeal 𝔪 (b := b))

variable (hb : b ⊔ 𝔪.fin = ⊤)

/-- Each actual dual unit orbit carries the inverse-character coefficient of its integral ideal. -/
theorem finiteHeckeFourierCoefficient_classFrequency (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (I : heckeDualClassIdeals 𝔪 hb0) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (heckeDualClassFrequency 𝔪 hb0 I : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _
          (heckeDualClassFrequency_ne_zero 𝔪 hb0 I))) : ℂ) =
      heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b * heckeValue 𝔪 ψ⁻¹ (I.1 : Ideal (𝓞 K)) := by
  rw [finiteHeckeFourierCoefficient_eq_dualHeckeValue 𝔪 hb0 hb ψ hψ,
    heckeDualFrequencyIdeal_classFrequency]

/-- The fixed ordinary class introduced by the conductor and codifferent. -/
def heckeDualClassShift : ClassGroup (𝓞 K) :=
  (ClassGroup.mk K (heckeDualIdealUnit 𝔪 (b := ⊤) (by simp)))⁻¹

/-- The inverse dual class is the fixed conductor/different shift times the base ideal class. -/
theorem heckeDualIdealUnit_class_inv :
    (ClassGroup.mk K (heckeDualIdealUnit 𝔪 hb0))⁻¹ =
      heckeDualClassShift 𝔪 * ClassGroup.mk0 ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩ := by
  let B : (Ideal (𝓞 K))⁰ := ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩
  have hu : heckeDualIdealUnit 𝔪 hb0 * FractionalIdeal.mk0 K B =
      heckeDualIdealUnit 𝔪 (b := ⊤) (by simp) := by
    apply Units.ext
    change Jdual * (b : FI) = FractionalIdeal.dual ℤ ℚ ((𝔪.fin * ⊤ : Ideal (𝓞 K)) : FI)
    exact heckeDualProductIdeal_mul_base 𝔪 hb0
  have hc := congrArg (ClassGroup.mk K) hu
  rw [map_mul, ClassGroup.mk_mk0] at hc
  change (ClassGroup.mk K (heckeDualIdealUnit 𝔪 hb0))⁻¹ =
    (ClassGroup.mk K (heckeDualIdealUnit 𝔪 (b := ⊤) (by simp)))⁻¹ * ClassGroup.mk0 B
  calc
    _ = (ClassGroup.mk K (heckeDualIdealUnit 𝔪 hb0))⁻¹ *
        ((ClassGroup.mk0 B)⁻¹ * ClassGroup.mk0 B) := by rw [inv_mul_cancel, mul_one]
    _ = (ClassGroup.mk K (heckeDualIdealUnit 𝔪 hb0) * ClassGroup.mk0 B)⁻¹ *
        ClassGroup.mk0 B := by rw [mul_inv_rev]; ac_rfl
    _ = _ := by rw [hc]

/-- The fixed shift followed by inversion permutes all ordinary ideal classes. -/
def heckeDualClassPermutation : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft (heckeDualClassShift 𝔪))

theorem heckeDualClassPermutation_apply (c : ClassGroup (𝓞 K)) :
    heckeDualClassPermutation 𝔪 c = heckeDualClassShift 𝔪 * c⁻¹ := rfl

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.norm_heckeDualClassFrequency
#print axioms GaloisForLFunctions.HeckeLFunctions.finiteHeckeFourierCoefficient_classFrequency
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualIdealUnit_class_inv
