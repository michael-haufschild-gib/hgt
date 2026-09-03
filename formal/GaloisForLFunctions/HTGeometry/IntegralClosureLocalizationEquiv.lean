import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral

/-!
# Localization commutes with integral closure, as a localized-base equivalence

Mathlib proves that integral closure commutes with localization at the level of
`IsLocalization`.  This module supplies the localized-base algebra structure and packages the
result as an algebra equivalence over an arbitrary localization model of the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable {Rf : Type v} [CommRing Rf] [IsDomain Rf]
variable {E : Type w} [Field E]
variable [Algebra R Rf] [Algebra R E] [Algebra Rf E] [IsScalarTower R Rf E]
variable (M : Submonoid R) [IsLocalization M Rf]

/-- Inclusion of the integral closure before base localization into the integral closure after
base localization. -/
def integralClosureLocalizationMap : integralClosure R E →+* integralClosure Rf E where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsDomain R] in
private theorem integralClosureLocalization_baseMapUnits
    (y : M) : IsUnit
      (((algebraMap (integralClosure R E)
        (Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M))).comp
        (algebraMap R (integralClosure R E))) y) := by
  let y' : Algebra.algebraMapSubmonoid (integralClosure R E) M :=
    ⟨algebraMap R (integralClosure R E) y, ⟨y, y.property, rfl⟩⟩
  exact IsLocalization.map_units
    (Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M)) y'

/-- The localization of an integral closure carries the algebra structure of any chosen
localization model of the base. -/
noncomputable instance integralClosureLocalization_baseAlgebra :
    Algebra Rf (Localization
      (Algebra.algebraMapSubmonoid (integralClosure R E) M)) :=
  (IsLocalization.lift
    (S := Rf)
    (P := Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M))
    (g := (algebraMap (integralClosure R E)
      (Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M))).comp
      (algebraMap R (integralClosure R E)))
    (integralClosureLocalization_baseMapUnits M)).toAlgebra

/-- The original base, its chosen localization model, and the localized integral closure form a
scalar tower. -/
instance integralClosureLocalization_baseTower :
    IsScalarTower R Rf (Localization
      (Algebra.algebraMapSubmonoid (integralClosure R E) M)) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.lift_eq
      (S := Rf)
      (P := Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M))
      (g := (algebraMap (integralClosure R E)
        (Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M))).comp
        (algebraMap R (integralClosure R E)))
      (integralClosureLocalization_baseMapUnits M) r).symm

/-- The localization of an integral closure is canonically equivalent, over the localized base,
to the integral closure after base localization. -/
noncomputable def integralClosureLocalizationAlgEquiv :
    Localization (Algebra.algebraMapSubmonoid (integralClosure R E) M) ≃ₐ[Rf]
      integralClosure Rf E := by
  let B := integralClosure R E
  let C := integralClosure Rf E
  let Bf := Localization (Algebra.algebraMapSubmonoid B M)
  letI : IsLocalization (Algebra.algebraMapSubmonoid E M) E :=
    IsLocalization.of_le_isUnit <| by
      rintro _ ⟨m, hm, rfl⟩
      change IsUnit (algebraMap R E m)
      rw [IsScalarTower.algebraMap_apply R Rf E]
      exact (IsLocalization.map_units Rf ⟨m, hm⟩).map (algebraMap Rf E)
  letI : Algebra B C :=
    (integralClosureLocalizationMap (R := R) (Rf := Rf) (E := E)).toAlgebra
  letI : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid B M) C :=
    IsLocalization.integralClosure M
  let eB : Bf ≃ₐ[B] C :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B M) Bf C
  refine AlgEquiv.ofRingEquiv (f := eB.toRingEquiv) ?_
  intro x
  have hhom : eB.toRingEquiv.toRingHom.comp (algebraMap Rf Bf) =
      algebraMap Rf C := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro r
    change eB (algebraMap Rf Bf (algebraMap R Rf r)) =
      algebraMap Rf C (algebraMap R Rf r)
    rw [← IsScalarTower.algebraMap_apply R Rf Bf,
      ← IsScalarTower.algebraMap_apply R Rf C,
      IsScalarTower.algebraMap_apply R B Bf,
      IsScalarTower.algebraMap_apply R B C,
      eB.commutes]
  exact DFunLike.congr_fun hhom x

end
end GaloisForLFunctions.HTGeometry
