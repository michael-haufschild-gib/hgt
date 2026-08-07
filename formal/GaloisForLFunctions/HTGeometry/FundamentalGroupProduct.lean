import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Product

/-!
# Fundamental group of a product

Path classes in a product are exactly pairs of path classes.  The equivalence respects the
fundamental-group multiplication (whose path-concatenation convention is reversed in mathlib).
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (x : X) (y : Y)

/-- Fundamental group of a product is the product of the fundamental groups. -/
noncomputable def fundamentalGroupProdMulEquiv :
    FundamentalGroup X x × FundamentalGroup Y y ≃*
      FundamentalGroup (X × Y) (x, y) where
  toFun p := Path.Homotopic.prod p.1 p.2
  invFun q := (Path.Homotopic.projLeft q, Path.Homotopic.projRight q)
  left_inv p := by
    ext
    · exact Path.Homotopic.projLeft_prod p.1 p.2
    · exact Path.Homotopic.projRight_prod p.1 p.2
  right_inv q := Path.Homotopic.prod_projLeft_projRight q
  map_mul' p q := by
    change Path.Homotopic.prod (q.1.trans p.1) (q.2.trans p.2) =
      (Path.Homotopic.prod q.1 q.2).trans (Path.Homotopic.prod p.1 p.2)
    exact (Path.Homotopic.comp_prod_eq_prod_comp q.1 q.2 p.1 p.2).symm

end GaloisForLFunctions.HTGeometry
