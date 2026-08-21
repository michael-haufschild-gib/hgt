import GaloisForLFunctions.HTGeometry.PointHomology
import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences induce isomorphisms on singular homology

A homotopy equivalence has a homotopy inverse, and homotopic maps induce the same map on homology,
so the two induced maps on homology are mutually inverse.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A homotopy equivalence induces an isomorphism on singular homology.** -/
theorem isIso_homologyMap_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (singMap R e.toFun) n) := by
  refine ⟨HomologicalComplex.homologyMap (singMap R e.invFun) n, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, ← singMap_comp,
      homologyMap_singMap_eq_of_homotopy R e.left_inv.some n, singMap_id,
      HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, ← singMap_comp,
      homologyMap_singMap_eq_of_homotopy R e.right_inv.some n, singMap_id,
      HomologicalComplex.homologyMap_id]

/-- A homeomorphism induces an isomorphism on singular homology. -/
theorem isIso_homologyMap_of_homeomorph (e : X ≃ₜ Y) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (singMap R (e : C(X, Y))) n) :=
  isIso_homologyMap_of_homotopyEquiv R e.toHomotopyEquiv n

end GaloisForLFunctions.HTGeometry
