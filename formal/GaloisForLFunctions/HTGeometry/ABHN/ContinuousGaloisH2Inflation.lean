import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisCohomology

/-!
# Inflation on finite continuous unit Galois `H²`

Ordinary group cohomology is contravariantly functorial in the group and covariantly functorial
in an equivariant coefficient map.  Transporting that map through the finite continuous-to-
ordinary comparison gives genuine maps on the continuous unit `H²` groups used by local class
field theory.

For a scalar tower `K ⊆ L ⊆ M` with `L/K` normal, restriction gives
`Gal(M/K) → Gal(L/K)` and the inclusion `Lˣ → Mˣ` is equivariant.  The resulting map is
the cohomological inflation of the relative `H²` layer split by `L` into the layer split by `M`.
It satisfies identity and composition without choosing local-invariant coordinates.
-/

open CategoryTheory
open Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Transport a finite continuous unit-`H²` class along a homomorphism of Galois groups and an
equivariant map of unit representations.  This is genuine cohomological functoriality, transported
through the finite continuous-to-ordinary comparison. -/
def finiteGaloisContinuousH2FunctorialMap
    (K₁ L₁ K₂ L₂ : Type)
    [Field K₁] [Field L₁] [Algebra K₁ L₁] [FiniteDimensional K₁ L₁]
    [Field K₂] [Field L₂] [Algebra K₂ L₂] [FiniteDimensional K₂ L₂]
    (f : Gal(L₂/K₂) →* Gal(L₁/K₁))
    (φ : Rep.res f (Rep.ofAlgebraAutOnUnits K₁ L₁) ⟶
      Rep.ofAlgebraAutOnUnits K₂ L₂) :
    continuousGaloisH2 K₁ L₁ →+ continuousGaloisH2 K₂ L₂ :=
  (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₂ L₂).symm.toAddMonoidHom.comp
    ((groupCohomology.map f φ 2).hom.toAddMonoidHom.comp
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₁ L₁).toAddMonoidHom)

/-- The functorial continuous map is exactly the ordinary cohomology map in ordinary coordinates. -/
theorem finiteGaloisContinuousH2FunctorialMap_toOrdinary_apply
    (K₁ L₁ K₂ L₂ : Type)
    [Field K₁] [Field L₁] [Algebra K₁ L₁] [FiniteDimensional K₁ L₁]
    [Field K₂] [Field L₂] [Algebra K₂ L₂] [FiniteDimensional K₂ L₂]
    (f : Gal(L₂/K₂) →* Gal(L₁/K₁))
    (φ : Rep.res f (Rep.ofAlgebraAutOnUnits K₁ L₁) ⟶
      Rep.ofAlgebraAutOnUnits K₂ L₂)
    (z : continuousGaloisH2 K₁ L₁) :
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₂ L₂
        (finiteGaloisContinuousH2FunctorialMap K₁ L₁ K₂ L₂ f φ z) =
      (groupCohomology.map f φ 2).hom
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₁ L₁ z) := by
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₂ L₂).apply_symm_apply _

/-- Identity law for functorial maps on finite continuous unit-`H²`. -/
theorem finiteGaloisContinuousH2FunctorialMap_id
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    finiteGaloisContinuousH2FunctorialMap K L K L (MonoidHom.id _) (𝟙 _) =
      AddMonoidHom.id _ := by
  ext z
  change (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm
    ((groupCohomology.map (MonoidHom.id Gal(L/K))
      (𝟙 (Rep.ofAlgebraAutOnUnits K L)) 2).hom
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) = z
  rw [groupCohomology.map_id]
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm_apply_apply z

/-- Composition law for functorial maps on finite continuous unit-`H²`. -/
theorem finiteGaloisContinuousH2FunctorialMap_comp
    (K₀ L₀ K₁ L₁ K₂ L₂ : Type)
    [Field K₀] [Field L₀] [Algebra K₀ L₀] [FiniteDimensional K₀ L₀]
    [Field K₁] [Field L₁] [Algebra K₁ L₁] [FiniteDimensional K₁ L₁]
    [Field K₂] [Field L₂] [Algebra K₂ L₂] [FiniteDimensional K₂ L₂]
    (f : Gal(L₁/K₁) →* Gal(L₀/K₀))
    (g : Gal(L₂/K₂) →* Gal(L₁/K₁))
    (φ : Rep.res f (Rep.ofAlgebraAutOnUnits K₀ L₀) ⟶
      Rep.ofAlgebraAutOnUnits K₁ L₁)
    (ψ : Rep.res g (Rep.ofAlgebraAutOnUnits K₁ L₁) ⟶
      Rep.ofAlgebraAutOnUnits K₂ L₂) :
    (finiteGaloisContinuousH2FunctorialMap K₁ L₁ K₂ L₂ g ψ).comp
        (finiteGaloisContinuousH2FunctorialMap K₀ L₀ K₁ L₁ f φ) =
      finiteGaloisContinuousH2FunctorialMap K₀ L₀ K₂ L₂ (f.comp g)
        ((Rep.resFunctor g).map φ ≫ ψ) := by
  ext z
  change (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₂ L₂).symm
      ((groupCohomology.map g ψ 2).hom
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₁ L₁
          ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₁ L₁).symm
            ((groupCohomology.map f φ 2).hom
              (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₀ L₀ z))))) =
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₂ L₂).symm
      ((groupCohomology.map (f.comp g) ((Rep.resFunctor g).map φ ≫ ψ) 2).hom
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₀ L₀ z))
  rw [(finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K₁ L₁).apply_symm_apply]
  rw [groupCohomology.map_comp]
  rfl

/-- Inclusion of units in a normal scalar tower, as an equivariant morphism for Galois
restriction. -/
def galoisTowerUnitsRepresentationHom
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (Rep.ofAlgebraAutOnUnits K L) ⟶
      Rep.ofAlgebraAutOnUnits K M :=
  Rep.ofHom ⟨(Units.map (algebraMap L M)).toAdditive.toIntLinearMap, by
    intro g
    ext u
    exact AlgEquiv.restrictNormal_commutes g L ((Additive.toMul u : Lˣ) : L)
  ⟩

/-- Unit-representation inclusions compose through a scalar tower. -/
theorem galoisTowerUnitsRepresentationHom_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [Normal K L] [Normal K M] :
    (((Rep.resFunctor
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M)).map
        (galoisTowerUnitsRepresentationHom K L M)) ≫
          galoisTowerUnitsRepresentationHom K M N).hom.toLinearMap =
      (galoisTowerUnitsRepresentationHom K L N).hom.toLinearMap := by
  ext u
  simp only [galoisTowerUnitsRepresentationHom]
  change Additive.ofMul
      (Units.map (algebraMap M N).toMonoidHom
        (Units.map (algebraMap L M).toMonoidHom (Additive.toMul u))) =
    Additive.ofMul (Units.map (algebraMap L N).toMonoidHom (Additive.toMul u))
  apply Additive.toMul.injective
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply L M N ((Additive.toMul u : Lˣ) : L)).symm

/-- Unit inclusion into the same field is the identity coefficient map. -/
theorem galoisTowerUnitsRepresentationHom_self
    (K L : Type) [Field K] [Field L] [Algebra K L] [Normal K L] :
    (galoisTowerUnitsRepresentationHom K L L).hom.toLinearMap =
      (Rep.Hom.hom (𝟙 (Rep.ofAlgebraAutOnUnits K L))).toLinearMap := by
  ext u
  simp only [galoisTowerUnitsRepresentationHom]
  change Additive.ofMul
    (Units.map (algebraMap L L).toMonoidHom (Additive.toMul u)) = u
  apply Additive.toMul.injective
  apply Units.ext
  simp

/-- Actual cohomological inflation along a finite normal scalar tower.  It is induced by restricting
`Gal(M/K)` to `Gal(L/K)` and including `Lˣ` into `Mˣ`; no invariant coordinates are chosen. -/
def finiteGaloisContinuousH2Inflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [FiniteDimensional K L] [FiniteDimensional K M] :
    continuousGaloisH2 K L →+ continuousGaloisH2 K M :=
  finiteGaloisContinuousH2FunctorialMap K L K M
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
    (galoisTowerUnitsRepresentationHom K L M)

/-- Actual inflation agrees with group-cohomological inflation in ordinary coordinates. -/
theorem finiteGaloisContinuousH2Inflation_toOrdinary_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [FiniteDimensional K L] [FiniteDimensional K M]
    (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M
        (finiteGaloisContinuousH2Inflation K L M z) =
      (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) := by
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).apply_symm_apply _

/-- Inflating into the same finite normal extension is the identity. -/
theorem finiteGaloisContinuousH2Inflation_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [Normal K L] [FiniteDimensional K L] :
    finiteGaloisContinuousH2Inflation K L L = AddMonoidHom.id _ := by
  ext z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  change finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L
      (finiteGaloisContinuousH2Inflation K L L z) =
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z
  rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply]
  have hmap := groupCohomology.map_congr
    (AlgEquiv.restrictNormalHom_id K L)
    (galoisTowerUnitsRepresentationHom_self K L) 2
  rw [hmap, groupCohomology.map_id]
  rfl

/-- Inflation through a tower of finite normal layers is transitive. -/
theorem finiteGaloisContinuousH2Inflation_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [Normal K L] [Normal K M]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N] :
    (finiteGaloisContinuousH2Inflation K M N).comp
        (finiteGaloisContinuousH2Inflation K L M) =
      finiteGaloisContinuousH2Inflation K L N := by
  ext z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K N).injective
  change finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K N
      (finiteGaloisContinuousH2Inflation K M N
        (finiteGaloisContinuousH2Inflation K L M z)) =
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K N
      (finiteGaloisContinuousH2Inflation K L N z)
  rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply,
    finiteGaloisContinuousH2Inflation_toOrdinary_apply,
    finiteGaloisContinuousH2Inflation_toOrdinary_apply]
  rw [← CategoryTheory.comp_apply]
  rw [← groupCohomology.map_comp]
  have hmap := groupCohomology.map_congr
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp K L M N).symm
    (galoisTowerUnitsRepresentationHom_comp K L M N) 2
  rw [hmap]

end

end GaloisForLFunctions.HTGeometry.ABHN
