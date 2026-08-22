import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionFunctoriality

/-!
# Brauer groups under field isomorphism

A field isomorphism gives mutually inverse scalar-extension maps on Brauer groups.  This makes
Brauer data transportable across field identifications, rather than dependent on a particular
presentation of a local field or residue field.

This is a functoriality bridge only: it does not construct a local invariant or relate any Brauer
class to a Tate integral.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable section

/-- Scalar extension along a field isomorphism is an additive equivalence of Brauer groups. -/
noncomputable def brauerGroupAddEquivOfRingEquiv
    {K L : Type u} [Field K] [Field L] (e : K ≃+* L) :
    BrauerGroup.{u, u} K ≃+ BrauerGroup.{u, u} L := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Algebra L K := e.symm.toRingHom.toAlgebra
  refine
    { toFun := scalarExtensionBrauerMap K L
      invFun := scalarExtensionBrauerMap L K
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro x
    letI : IsScalarTower K L K := IsScalarTower.of_algebraMap_eq (fun x => by
      change x = e.symm (e x)
      simp)
    exact (scalarExtensionBrauerMap_comp K L K x).trans (scalarExtensionBrauerMap_id K x)
  · intro y
    letI : IsScalarTower L K L := IsScalarTower.of_algebraMap_eq (fun y => by
      change y = e (e.symm y)
      simp)
    exact (scalarExtensionBrauerMap_comp L K L y).trans (scalarExtensionBrauerMap_id L y)
  · intro x y
    exact (scalarExtensionBrauerAddHom K L).map_add x y

/-- On elements, `brauerGroupAddEquivOfRingEquiv` is scalar extension through the given field
isomorphism. -/
theorem brauerGroupAddEquivOfRingEquiv_apply
    {K L : Type u} [Field K] [Field L] (e : K ≃+* L) (x : BrauerGroup.{u, u} K) :
    brauerGroupAddEquivOfRingEquiv e x =
      @scalarExtensionBrauerMap K L _ _ e.toRingHom.toAlgebra x :=
  rfl

/-- The inverse transport is scalar extension through the inverse field isomorphism. -/
theorem brauerGroupAddEquivOfRingEquiv_symm_apply
    {K L : Type u} [Field K] [Field L] (e : K ≃+* L) (y : BrauerGroup.{u, u} L) :
    (brauerGroupAddEquivOfRingEquiv e).symm y =
      @scalarExtensionBrauerMap L K _ _ e.symm.toRingHom.toAlgebra y :=
  rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
