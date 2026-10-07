import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Explicit path transport of fundamental-group classes

These formulas retain the common conjugator when a whole packet moves between
basepoints. Mathlib multiplies fundamental-group classes in reverse path order.
-/

open Topology

namespace GaloisForLFunctions.HTGeometry

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem fundamentalGroup_transport_apply {x y : X} (p : Path x y)
    (q : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p q =
      (Path.Homotopic.Quotient.mk p).symm.trans
        (q.trans (Path.Homotopic.Quotient.mk p)) := rfl

theorem pathClass_map_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z)
    (f : C(X, Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) :=
  (FundamentalGroupoid.map f).map_comp p q

theorem pathClass_map_symm {x y : X} (p : Path.Homotopic.Quotient x y)
    (f : C(X, Y)) : (p.symm).map f = (p.map f).symm := by
  induction p using Quotient.inductionOn with
  | _ p => rfl

theorem pathClass_symm_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    (p.trans q).symm = q.symm.trans p.symm := by
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q => exact congrArg Path.Homotopic.Quotient.mk (Path.trans_symm p q)

theorem pathClass_symm_symm {x y : X} (p : Path.Homotopic.Quotient x y) :
    p.symm.symm = p := by
  induction p using Quotient.inductionOn with
  | _ p => exact congrArg Path.Homotopic.Quotient.mk (Path.symm_symm p)

private theorem trans_symm_cancel {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient x z) :
    p.trans (p.symm.trans q) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

/-- Mapping commutes with simultaneous basepoint transport of a loop packet. -/
theorem fundamentalGroup_map_transport {x y : X} (p : Path x y)
    (q : FundamentalGroup X x) (f : C(X, Y)) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath p q) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x q) := by
  change ((Path.Homotopic.Quotient.mk p).symm.trans
      (q.trans (Path.Homotopic.Quotient.mk p))).map f = _
  rw [pathClass_map_trans, pathClass_map_trans, pathClass_map_symm]
  rfl

/-- Comparing two transport paths gives one inner conjugator for every loop. -/
theorem fundamentalGroup_transport_compare {x y : X} (p r : Path x y)
    (q : FundamentalGroup X x) :
    let c : FundamentalGroup X y := .fromPath ⟦r.symm.trans p⟧
    FundamentalGroup.fundamentalGroupMulEquivOfPath p q =
      c * FundamentalGroup.fundamentalGroupMulEquivOfPath r q * c⁻¹ := by
  dsimp only
  change (Path.Homotopic.Quotient.mk p).symm.trans
      (q.trans (Path.Homotopic.Quotient.mk p)) =
    ((Path.Homotopic.Quotient.mk r).symm.trans (Path.Homotopic.Quotient.mk p)).symm.trans
      (((Path.Homotopic.Quotient.mk r).symm.trans
        (q.trans (Path.Homotopic.Quotient.mk r))).trans
          ((Path.Homotopic.Quotient.mk r).symm.trans (Path.Homotopic.Quotient.mk p)))
  simp only [pathClass_symm_trans, pathClass_symm_symm,
    Path.Homotopic.Quotient.trans_assoc, trans_symm_cancel]

end GaloisForLFunctions.HTGeometry
