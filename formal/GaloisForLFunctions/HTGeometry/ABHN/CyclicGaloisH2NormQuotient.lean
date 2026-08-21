/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldNormSequence

/-!
# Cyclic degree-two cohomology as a norm quotient

For a finite cyclic Galois extension `L/K`, the degree-two Galois cohomology of units is the
quotient of `Kˣ` by norms from `Lˣ`.  This is the cohomological form of the cyclic-algebra
parameter group and a direct precursor to local class field theory.  It does not yet identify
this cohomology group with a Brauer group or construct local reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- Base-field units, viewed as the fixed units in the cyclic degree-two resolution. -/
noncomputable def cyclicGaloisH2FixedUnitsBaseAddHom [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ →+ cyclicGaloisH2FixedUnits K L where
  toFun := fun a => ⟨cyclicGaloisBaseUnitsMap (K := K) (L := L) a, by
    change Additive.ofMul (Units.map (cyclicGaloisGenerator K L).toMonoidHom
        (Units.map (algebraMap K L) a.toMul)) -
        Additive.ofMul (Units.map (algebraMap K L) a.toMul) = 0
    have hfixed : Units.map (cyclicGaloisGenerator K L).toMonoidHom
        (Units.map (algebraMap K L) a.toMul) =
          Units.map (algebraMap K L) a.toMul := by
      apply Units.ext
      exact (cyclicGaloisGenerator K L).commutes _
    rw [hfixed, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add _ _ _

/-- Every fixed unit in the cyclic degree-two resolution comes from a base-field unit. -/
theorem cyclicGaloisH2FixedUnitsBaseAddHom_surjective [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (cyclicGaloisH2FixedUnitsBaseAddHom K L) := by
  intro x
  obtain ⟨y, hy⟩ := cyclicGaloisH2FixedUnit_exists_base_unit K L x
  refine ⟨Additive.ofMul y, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  change Units.map (algebraMap K L) y = cyclicGaloisH2FixedUnit K L x
  exact hy

/-- The base-field embedding is injective on cyclic degree-two fixed-unit representatives. -/
theorem cyclicGaloisH2FixedUnitsBaseAddHom_injective [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (cyclicGaloisH2FixedUnitsBaseAddHom K L) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  have hval := congrArg Subtype.val hxy
  have hunits := congrArg Additive.toMul hval
  exact congrArg Units.val hunits

/-- The cyclic fixed-unit representatives are canonically the additive presentation of `Kˣ`. -/
noncomputable def cyclicGaloisH2FixedUnitsBaseAddEquiv [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ ≃+ cyclicGaloisH2FixedUnits K L :=
  AddEquiv.ofBijective (cyclicGaloisH2FixedUnitsBaseAddHom K L)
    ⟨cyclicGaloisH2FixedUnitsBaseAddHom_injective K L,
      cyclicGaloisH2FixedUnitsBaseAddHom_surjective K L⟩

/-- The cyclic degree-two projection expressed directly on base-field units. -/
noncomputable def cyclicGaloisH2BaseProjection [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ →+ cyclicGaloisH2 K L :=
  (cyclicGaloisH2Projection K L).comp (cyclicGaloisH2FixedUnitsBaseAddHom K L)

/-- Every cyclic degree-two cohomology class has a base-field-unit representative. -/
theorem cyclicGaloisH2BaseProjection_surjective [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (cyclicGaloisH2BaseProjection K L) := by
  intro z
  obtain ⟨x, hx⟩ := cyclicGaloisH2Projection_surjective K L z
  obtain ⟨y, hy⟩ := cyclicGaloisH2FixedUnitsBaseAddHom_surjective K L x
  exact ⟨y, by rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply, hy, hx]⟩

/-- The additive subgroup of base-field units that are norms from the cyclic extension. -/
noncomputable def cyclicGaloisH2BaseNormImage [FiniteDimensional K L] :
    AddSubgroup (Additive Kˣ) :=
  (cyclicGaloisAdditiveNormUnits K L).range

/-- Norms are exactly the base-field units representing zero in cyclic degree-two cohomology. -/
theorem cyclicGaloisH2BaseNormImage_eq_ker [FiniteDimensional K L] [IsGalois K L] :
    cyclicGaloisH2BaseNormImage K L = (cyclicGaloisH2BaseProjection K L).ker := by
  ext a
  rw [AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply]
    apply (cyclicGaloisH2Projection_eq_zero_iff_exists_field_norm K L _).mpr
    refine ⟨Additive.toMul y, ?_⟩
    change cyclicGaloisH2FixedUnit K L (cyclicGaloisH2FixedUnitsBaseAddHom K L a) =
      Units.map (algebraMap K L)
        (cyclicGaloisNormUnits K L (Additive.toMul y))
    have hbase : cyclicGaloisH2FixedUnit K L (cyclicGaloisH2FixedUnitsBaseAddHom K L a) =
        Units.map (algebraMap K L) (Additive.toMul a) := by
      rfl
    rw [hbase]
    apply Units.ext
    change algebraMap K L ((Additive.toMul a : Kˣ) : K) =
      algebraMap K L ((cyclicGaloisNormUnits K L (Additive.toMul y) : Kˣ) : K)
    simpa [cyclicGaloisAdditiveNormUnits] using
      congrArg (algebraMap K L) (congrArg Units.val (congrArg Additive.toMul hy).symm)
  · intro ha
    rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply] at ha
    obtain ⟨y, hy⟩ :=
      (cyclicGaloisH2Projection_eq_zero_iff_exists_field_norm K L
        (cyclicGaloisH2FixedUnitsBaseAddHom K L a)).mp ha
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective K L
    have hbase : cyclicGaloisH2FixedUnit K L (cyclicGaloisH2FixedUnitsBaseAddHom K L a) =
        Units.map (algebraMap K L) (Additive.toMul a) := by
      rfl
    rw [hbase] at hy
    exact congrArg Units.val hy.symm

/-- **Cyclic degree-two norm quotient.** For a finite cyclic Galois extension, unit cohomology
in degree two is the base-field unit group modulo norms from the extension. -/
noncomputable def cyclicGaloisH2BaseNormQuotientEquiv [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ cyclicGaloisH2 K L :=
  (QuotientAddGroup.quotientAddEquivOfEq (cyclicGaloisH2BaseNormImage_eq_ker K L)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (cyclicGaloisH2BaseProjection K L)
      (cyclicGaloisH2BaseProjection_surjective K L))

end GaloisForLFunctions.HTGeometry.ABHN
