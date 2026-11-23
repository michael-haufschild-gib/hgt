import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi

/-! A reduced finite fibre over a perfect field stays reduced after a
finite unramified pullback. -/

noncomputable section

namespace GlobalTheory.SchemeCohomology

/-- A reduced finite algebra over a perfect field has no relative
Kähler differentials, since it is a product of finite separable fields. -/
theorem formallyUnramified_of_finite_reduced (k A : Type*) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] :
    Algebra.FormallyUnramified k A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  letI : Finite (MaximalSpectrum A) := inferInstance
  haveI : Algebra.FormallyUnramified k (∀ m : MaximalSpectrum A, A ⧸ m.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro m
    letI : m.asIdeal.IsMaximal := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable k _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars k).symm

/-- Unramified pullback preserves the reducedness of a finite fibre. -/
theorem isReduced_quotient_map_of_formallyUnramified (k : Type*) [Field k] [PerfectField k]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Algebra.FormallyUnramified A B] (I : Ideal A)
    [Module.Finite k (A ⧸ I)] [IsReduced (A ⧸ I)]
    [Module.Finite k (B ⧸ I.map (algebraMap A B))] :
    IsReduced (B ⧸ I.map (algebraMap A B)) := by
  let J := I.map (algebraMap A B)
  let P := A ⧸ I
  let Q := B ⧸ J
  letI : Algebra P Q := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  letI : IsScalarTower A P Q := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k P Q := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k A P, ← IsScalarTower.algebraMap_apply A P Q]
    rw [IsScalarTower.algebraMap_apply A B Q, ← IsScalarTower.algebraMap_apply k A B,
      ← IsScalarTower.algebraMap_apply k B Q]
  letI : Algebra.FormallyUnramified k P := formallyUnramified_of_finite_reduced k P
  letI : Algebra.FormallyUnramified B Q :=
    .of_surjective (Ideal.Quotient.mkₐ B J) Ideal.Quotient.mk_surjective
  letI : Algebra.FormallyUnramified A Q := .comp A B Q
  letI : Algebra.FormallyUnramified P Q := .of_restrictScalars A P Q
  letI : Algebra.FormallyUnramified k Q := .comp k P Q
  exact Algebra.FormallyUnramified.isReduced_of_field k Q

end GlobalTheory.SchemeCohomology
