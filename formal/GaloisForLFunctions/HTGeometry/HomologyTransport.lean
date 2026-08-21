import GaloisForLFunctions.HTGeometry.PairSequence
import GaloisForLFunctions.HTGeometry.TopologyHelpers

/-!
# Transporting vanishing homology

Vanishing of homology passes along homeomorphisms and homotopy equivalences, and between the chains
of a subspace and the chains supported in it.  These are the three transports the puncturing
induction uses to feed contractibility of the two star-shaped pieces into the long exact sequences.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The homology of a space and of a homotopy equivalent one agree. -/
noncomputable def homologyIsoOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (singChainComplex R X).homology n ≅ (singChainComplex R Y).homology n :=
  haveI := isIso_homologyMap_of_homotopyEquiv R e n
  asIso (HomologicalComplex.homologyMap (singMap R e.toFun) n)

theorem isZero_homology_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (h : IsZero ((singChainComplex R Y).homology n)) :
    IsZero ((singChainComplex R X).homology n) :=
  h.of_iso (homologyIsoOfHomotopyEquiv R e n)

/-- The homology of a subspace and of the chains supported in it agree. -/
noncomputable def homologyIsoSubcomplex (S : Set X) (n : ℕ) :
    (subcomplexOfSubset R S).complex.homology n ≅ (singChainComplex R ↥S).homology n :=
  haveI : IsIso (HomologicalComplex.homologyMap (subspaceChainMap R S) n) :=
    inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor (ModuleCat R)
      (ComplexShape.down ℕ) n).map (subspaceChainMap R S)))
  (asIso (HomologicalComplex.homologyMap (subspaceChainMap R S) n)).symm

theorem isZero_homology_subcomplexOfSubset (S : Set X) (n : ℕ)
    (h : IsZero ((singChainComplex R ↥S).homology n)) :
    IsZero ((subcomplexOfSubset R S).complex.homology n) :=
  h.of_iso (homologyIsoSubcomplex R S n)

end GaloisForLFunctions.HTGeometry
