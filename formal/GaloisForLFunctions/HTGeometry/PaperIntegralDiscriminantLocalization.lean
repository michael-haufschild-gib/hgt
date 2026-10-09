import GaloisForLFunctions.HTGeometry.PaperIntegralNormalDiscriminant
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The discriminant complement retains the actual normal coefficient algebra

The proved source normal embedding remains injective after the integral
discriminant is inverted. Regularity of the coefficient discriminant also
shows that passing to this open part of the normal ring kills no original
coefficient polynomial, over any commutative base ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

private abbrev integralDiscriminantNormalRing {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (PaperIdealAssociatedGraded I) := inferInstance

local instance : CommRing (PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n)) :=
  integralDiscriminantNormalRing _

/-- The coefficient ring with the integral generic discriminant inverted. -/
abbrev PaperDiscriminantCoefficientOpen :=
  Localization.Away (paperIntegralDiscriminantPolynomial K n)

/-- The actual normal ring with its integral discriminant inverted. -/
abbrev PaperDiscriminantNormalOpen :=
  Localization.Away (paperIntegralNormalDiscriminant K n)

/-- The source normal embedding extended to the discriminant complements. -/
def paperDiscriminantOpenEmbedding :
    PaperDiscriminantCoefficientOpen K n →ₐ[K] PaperDiscriminantNormalOpen K n :=
  Localization.awayMapₐ (paperElementarySymmetricNormalMap K n)
    (paperIntegralDiscriminantPolynomial K n)

/-- Inverting the discriminant preserves the full coefficient-localization embedding. -/
theorem paperDiscriminantOpenEmbedding_injective :
    Function.Injective (paperDiscriminantOpenEmbedding K n) := by
  change Function.Injective (Localization.awayMapₐ (paperElementarySymmetricNormalMap K n)
    (paperIntegralDiscriminantPolynomial K n))
  exact IsLocalization.Away.mapₐ_injective_of_injective (paperIntegralDiscriminantPolynomial K n)
    (f := paperElementarySymmetricNormalMap K n)
    (paperElementarySymmetricNormalMap_injective K n)

/-- The localized embedding sends each coefficient polynomial to its actual normal image. -/
theorem paperDiscriminantOpenEmbedding_algebraMap (p : MvPolynomial (Fin n) K) :
    paperDiscriminantOpenEmbedding K n
      (algebraMap (MvPolynomial (Fin n) K) (PaperDiscriminantCoefficientOpen K n) p) =
        algebraMap (PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n))
          (PaperDiscriminantNormalOpen K n) (paperElementarySymmetricNormalMap K n p) :=
  IsLocalization.map_eq
    (M := Submonoid.powers (paperIntegralDiscriminantPolynomial K n))
    (T := Submonoid.powers (paperIntegralNormalDiscriminant K n))
    (S := PaperDiscriminantCoefficientOpen K n) (Q := PaperDiscriminantNormalOpen K n)
    (g := (paperElementarySymmetricNormalMap K n).toRingHom)
    (by
      rintro x ⟨m, rfl⟩
      exact ⟨m, (map_pow (paperElementarySymmetricNormalMap K n)
        (paperIntegralDiscriminantPolynomial K n) m).symm⟩) p

/-- The coefficient ring itself embeds in its discriminant complement over every base ring. -/
theorem paperDiscriminantCoefficientOpen_injective :
    Function.Injective
      (algebraMap (MvPolynomial (Fin n) K) (PaperDiscriminantCoefficientOpen K n)) := by
  apply IsLocalization.injective (M := Submonoid.powers (paperIntegralDiscriminantPolynomial K n))
  rintro x ⟨m, rfl⟩
  exact isRegular_iff_mem_nonZeroDivisors.mp
    ((paperIntegralDiscriminantPolynomial_regular K n).pow m)

/-- The original coefficient polynomial algebra inside the actual discriminant-open normal ring. -/
def paperDiscriminantOpenCoefficientMap :
    MvPolynomial (Fin n) K →ₐ[K] PaperDiscriminantNormalOpen K n :=
  (IsScalarTower.toAlgHom K
    (PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n))
    (PaperDiscriminantNormalOpen K n)).comp (paperElementarySymmetricNormalMap K n)

/-- Removing the collision divisor introduces no relation among original coefficient polynomials. -/
theorem paperDiscriminantOpenCoefficientMap_injective :
    Function.Injective (paperDiscriminantOpenCoefficientMap K n) := by
  intro p q h
  apply paperDiscriminantCoefficientOpen_injective K n
  apply paperDiscriminantOpenEmbedding_injective K n
  rw [paperDiscriminantOpenEmbedding_algebraMap, paperDiscriminantOpenEmbedding_algebraMap]
  exact h

/-- Exact vanishing is retained after passage to the actual discriminant complement. -/
theorem paperDiscriminantOpenCoefficientMap_eq_zero_iff (p : MvPolynomial (Fin n) K) :
    paperDiscriminantOpenCoefficientMap K n p = 0 ↔ p = 0 := by
  constructor
  · intro h
    exact paperDiscriminantOpenCoefficientMap_injective K n
      (h.trans (map_zero (paperDiscriminantOpenCoefficientMap K n)).symm)
  · rintro rfl
    exact map_zero _

end

end GaloisForLFunctions.HTGeometry
