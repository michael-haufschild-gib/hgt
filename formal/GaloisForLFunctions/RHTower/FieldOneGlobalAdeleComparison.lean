import GaloisForLFunctions.RHTower.FieldOneRationalPrimaryReciprocity
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# The rational global adele ring behind the archimedean--finite carrier

The product `ℝ × FieldOneFiniteAdele` used by the field-one Weyl construction is the full
additive adele ring of `ℚ`, not a finite-place semilocal ring.  This file makes that distinction
formal by identifying it with mathlib's `NumberField.AdeleRing ℤ ℚ`.

The comparison is simultaneously a ring equivalence and a homeomorphism, with identical
underlying functions.  It preserves principal rational adeles.  Transporting the standard
archimedean--finite additive character therefore gives a nontrivial character of the global
adele ring that vanishes on every principal rational adele.

No quotient by `S`-units and no multiplicative idele-class scaling action is constructed here.
Those are separate requirements in the Connes--Consani semilocal trace space.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open NumberField NumberField.InfinitePlace

/-- The unique infinite completion of `ℚ` is the real field. -/
def fieldOneInfiniteAdeleRingEquivReal :
    NumberField.InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique
      (fun v : NumberField.InfinitePlace ℚ => v.Completion)).trans
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (by
        simpa only [Subsingleton.elim
          (default : NumberField.InfinitePlace ℚ) Rat.infinitePlace] using
          Rat.isReal_infinitePlace))

/-- Mathlib's rational adele ring is the archimedean--finite product used by the
field-one global additive carrier. -/
def fieldOneGlobalAdeleRingEquiv :
    NumberField.AdeleRing ℤ ℚ ≃+*
      (ℝ × FieldOneFiniteAdele) :=
  RingEquiv.prodCongr
    fieldOneInfiniteAdeleRingEquivReal
    (RingEquiv.refl FieldOneFiniteAdele)

/-- Topological version of the unique infinite-completion comparison. -/
def fieldOneInfiniteAdeleRingHomeomorphReal :
    NumberField.InfiniteAdeleRing ℚ ≃ₜ ℝ :=
  (Homeomorph.piUnique
      (fun v : NumberField.InfinitePlace ℚ => v.Completion)).trans
    (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
      (by
        simpa only [Subsingleton.elim
          (default : NumberField.InfinitePlace ℚ) Rat.infinitePlace] using
          Rat.isReal_infinitePlace)).toHomeomorph

/-- The global adele comparison is also a homeomorphism. -/
def fieldOneGlobalAdeleRingHomeomorph :
    NumberField.AdeleRing ℤ ℚ ≃ₜ
      (ℝ × FieldOneFiniteAdele) :=
  Homeomorph.prodCongr
    fieldOneInfiniteAdeleRingHomeomorphReal
    (Homeomorph.refl FieldOneFiniteAdele)

/-- Ring and topological comparisons have the same underlying function. -/
theorem fieldOneGlobalAdeleRingHomeomorph_apply
    (x : NumberField.AdeleRing ℤ ℚ) :
    fieldOneGlobalAdeleRingHomeomorph x =
      fieldOneGlobalAdeleRingEquiv x :=
  rfl

/-- The global comparison preserves the diagonal embedding of `ℚ`. -/
theorem fieldOneGlobalAdeleRingEquiv_principal
    (q : ℚ) :
    fieldOneGlobalAdeleRingEquiv
        (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ) q) =
      algebraMap ℚ (ℝ × FieldOneFiniteAdele) q := by
  have h :
      fieldOneGlobalAdeleRingEquiv.toRingHom.comp
          (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)) =
        algebraMap ℚ (ℝ × FieldOneFiniteAdele) :=
    Subsingleton.elim _ _
  exact DFunLike.congr_fun h q

/-- Standard additive-circle character on mathlib's rational global adele ring. -/
def fieldOneGlobalAdeleStandardUnitAddCircleCharacter :
    NumberField.AdeleRing ℤ ℚ →+ UnitAddCircle :=
  fieldOneSemilocalStandardUnitAddCircleCharacter.comp
    fieldOneGlobalAdeleRingEquiv.toRingHom.toAddMonoidHom

/-- The archimedean--finite standard character is nontrivial. -/
theorem fieldOneSemilocalStandardUnitAddCircleCharacter_ne_zero :
    fieldOneSemilocalStandardUnitAddCircleCharacter ≠ 0 := by
  intro h
  apply fieldOneFiniteAdeleStandardUnitAddCircleCharacter_ne_zero
  ext a
  have ha := DFunLike.congr_fun h (0, a)
  simpa [fieldOneSemilocalStandardUnitAddCircleCharacter] using ha

/-- Global additive reciprocity: the standard character vanishes on principal
rational adeles. -/
theorem fieldOneGlobalAdeleStandardUnitAddCircleCharacter_principal
    (q : ℚ) :
    fieldOneGlobalAdeleStandardUnitAddCircleCharacter
        (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ) q) = 0 := by
  change
    fieldOneSemilocalStandardUnitAddCircleCharacter
        (fieldOneGlobalAdeleRingEquiv
          (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ) q)) = 0
  rw [fieldOneGlobalAdeleRingEquiv_principal]
  exact fieldOneSemilocalStandardUnitAddCircleCharacter_diagonal_rat q

/-- The transported standard global adele character is nontrivial. -/
theorem fieldOneGlobalAdeleStandardUnitAddCircleCharacter_ne_zero :
    fieldOneGlobalAdeleStandardUnitAddCircleCharacter ≠ 0 := by
  intro h
  apply fieldOneSemilocalStandardUnitAddCircleCharacter_ne_zero
  ext y
  have hy :=
    DFunLike.congr_fun h
      (fieldOneGlobalAdeleRingEquiv.symm y)
  simpa [fieldOneGlobalAdeleStandardUnitAddCircleCharacter] using hy

end

end GaloisForLFunctions.RHTower
