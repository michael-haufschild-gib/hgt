import GaloisForLFunctions.HTGeometry.FundamentalGroupTransport

open Topology

namespace GaloisForLFunctions.HTGeometry

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem fundamentalGroup_mapOfEq_mk (f : C(X, Y)) {x : X} {y : Y}
    (hx : f x = y) (p : Path x x) :
    FundamentalGroup.mapOfEq f hx (FundamentalGroup.fromPath ⟦p⟧) =
      FundamentalGroup.fromPath ⟦(p.map f.continuous).cast hx.symm hx.symm⟧ := by
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

/-- A single connecting path conjugates every member of a pointed loop packet. -/
theorem fundamentalGroup_mapOfEq_transport (f : C(X, Y)) {x s : X} {y : Y}
    (hx : f x = y) (hs : f s = y) (α : Path x s) (p : Path s s) :
    let g : FundamentalGroup Y y := .fromPath
      ⟦(α.map f.continuous).cast hx.symm hs.symm⟧
    FundamentalGroup.mapOfEq f hx
      (FundamentalGroup.fundamentalGroupMulEquivOfPath α.symm
        (FundamentalGroup.fromPath ⟦p⟧)) =
      g⁻¹ * FundamentalGroup.mapOfEq f hs (FundamentalGroup.fromPath ⟦p⟧) * g := by
  dsimp only
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  rw [fundamentalGroup_transport_apply]
  change (((Path.Homotopic.Quotient.mk α).symm.symm.trans
    ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk α).symm)).map f).cast
      hx.symm hx.symm = _
  rw [pathClass_symm_symm]
  change Path.Homotopic.Quotient.mk
      (((α.trans (p.trans α.symm)).map f.continuous).cast hx.symm hx.symm) =
    Path.Homotopic.Quotient.mk
      (((α.map f.continuous).cast hx.symm hs.symm).trans
        (((p.map f.continuous).cast hs.symm hs.symm).trans
          ((α.map f.continuous).cast hx.symm hs.symm).symm))
  apply congrArg Path.Homotopic.Quotient.mk
  rw [Path.map_trans, Path.map_trans,
    Path.cast_trans _ _ hx.symm hs.symm hx.symm,
    Path.cast_trans _ _ hs.symm hs.symm hx.symm]
  rfl

/-- Nullhomotopy survives transport even when the endpoint images differ. -/
theorem fundamentalGroup_mapOfEq_transport_null (f : C(X, Y)) {x s : X} {y : Y}
    (hx : f x = y) (α : Path x s) (p : Path s s)
    (hp : (p.map f.continuous).Homotopic (Path.refl (f s))) :
    FundamentalGroup.mapOfEq f hx
      (FundamentalGroup.fundamentalGroupMulEquivOfPath α.symm
        (FundamentalGroup.fromPath ⟦p⟧)) = 1 := by
  have hp' : FundamentalGroup.map f s (FundamentalGroup.fromPath ⟦p⟧) = 1 :=
    Quotient.sound hp
  have hh := fundamentalGroup_map_transport α.symm
    (FundamentalGroup.fromPath ⟦p⟧) f
  rw [hp', map_one] at hh
  subst y
  rw [FundamentalGroup.mapOfEq_apply]
  exact hh

end GaloisForLFunctions.HTGeometry
