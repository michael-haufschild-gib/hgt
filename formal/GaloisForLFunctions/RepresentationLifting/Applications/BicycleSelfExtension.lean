import GaloisForLFunctions.RepresentationLifting.ChainSelfExtension
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Homological.BBChainComplex

/-!+# Square-zero self-extensions of bivariate bicycle codes

The original convolution boundaries form a three-term module complex. The canonical
dual-number self-extension therefore gives an equivariant lift of its total boundary for
every pair of bicycle polynomials over every finite abelian translation group.
The construction uses the proved boundary relation and does not require acyclicity.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

open Quantum.Stabilizer.Homological.BB

variable {G : Type} [Fintype G] [AddCommGroup G] (A B : G → ZMod 2)

/-- The existing bicycle-code boundaries as a categorical short complex. -/
def bicycleBoundaryComplex : ShortComplex (ModuleCat (ZMod 2)) where
  X₁ := ModuleCat.of (ZMod 2) (G → ZMod 2)
  X₂ := ModuleCat.of (ZMod 2) (G × Fin 2 → ZMod 2)
  X₃ := ModuleCat.of (ZMod 2) (G → ZMod 2)
  f := ModuleCat.ofHom (bbBoundary2 A B)
  g := ModuleCat.ofHom (bbBoundary1 A B)
  zero := ModuleCat.hom_ext (bbBoundary_comp A B)

/-- Every bicycle code has the canonical exact extension of its total boundary module. -/
theorem bicycle_detector_exact :
    Function.Injective (detectorInclusion (bicycleBoundaryComplex A B)) ∧
      LinearMap.range (detectorInclusion (bicycleBoundaryComplex A B)) =
        LinearMap.ker (detectorProjection (bicycleBoundaryComplex A B)) ∧
      Function.Surjective (detectorProjection (bicycleBoundaryComplex A B)) :=
  detector_exact _

/-- The detector projects to the original two convolution boundaries. -/
theorem bicycle_detector_lifts (v : ChainTotal (bicycleBoundaryComplex A B)) :
    detectorProjection (bicycleBoundaryComplex A B)
        (detectorLift (bicycleBoundaryComplex A B) v) =
      (0, bbBoundary2 A B v.1, bbBoundary1 A B v.2.1) :=
  detectorProjection_lift _ v

/-- The lifted boundary is equivariant for multiplication by the dual-number parameter. -/
theorem bicycle_detector_equivariant (v : ChainTotal (bicycleBoundaryComplex A B)) :
    detectorDifferential (bicycleBoundaryComplex A B)
        (detectorLift (bicycleBoundaryComplex A B) v) =
      detectorLift (bicycleBoundaryComplex A B)
        (0, bbBoundary2 A B v.1, bbBoundary1 A B v.2.1) :=
  detectorLift_intertwines _ v

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.bicycle_detector_exact
#print axioms GaloisForLFunctions.RepresentationLifting.bicycle_detector_lifts
#print axioms GaloisForLFunctions.RepresentationLifting.bicycle_detector_equivariant
