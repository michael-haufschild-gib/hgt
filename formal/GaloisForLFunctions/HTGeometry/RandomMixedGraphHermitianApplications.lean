import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.GraphLocalHallAssembly
import GaloisForLFunctions.HTGeometry.StokesSpectralWittObstruction
import GaloisForLFunctions.HTGeometry.HankelTerminalFlux
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.HypergraphProjectiveSpectralFactorization
import GaloisForLFunctions.HTGeometry.SiteFactorInteractionCoordinates
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.HermitianKnobRelationPolynomial
import GaloisForLFunctions.HTGeometry.HypergraphLocalHamiltonian

open Matrix

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

theorem graphLocalEdgeMatrix_mixedGraph_reconstruction
    {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (G : SimpleGraph I) (p : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨graphLocalEdgeMatrix I R G p, graphLocalEdgeMatrix_isHermitian G p⟩)
        (hermitianDirectedPart
          ⟨graphLocalEdgeMatrix I R G p, graphLocalEdgeMatrix_isHermitian G p⟩) =
      graphLocalEdgeMatrix I R G p :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨graphLocalEdgeMatrix I R G p, graphLocalEdgeMatrix_isHermitian G p⟩

theorem finitePauliMatrix_mixedGraph_reconstruction
    {σ : Type*} [Fintype σ] [DecidableEq σ] (P : σ → Option (Fin 3)) :
    mixedHermitianMatrix
        (hermitianUndirectedPart ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩)
        (hermitianDirectedPart ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩) =
      finitePauliMatrix P :=
  mixedHermitianMatrix_parts_reconstruct ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩

theorem chainPauliFin_mixedGraph_reconstruction
    (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) :
    mixedHermitianMatrix
        (hermitianUndirectedPart ⟨chainPauliFin n a, chainPauliFin_isHermitian n a⟩)
        (hermitianDirectedPart ⟨chainPauliFin n a, chainPauliFin_isHermitian n a⟩) =
      chainPauliFin n a :=
  mixedHermitianMatrix_parts_reconstruct ⟨chainPauliFin n a, chainPauliFin_isHermitian n a⟩

theorem hypergraphGeneratorFin_mixedGraph_reconstruction
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [(v : V) → Fintype (A v)] [(v : V) → DecidableEq (A v)]
    [∀ v, Nonempty (A v)] (𝔥 : Finset (Finset V))
    (j : Fin (hypergraphCoordinateCount A 𝔥)) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨hypergraphGeneratorFin A 𝔥 j, hypergraphGeneratorFin_isHermitian A 𝔥 j⟩)
        (hermitianDirectedPart
          ⟨hypergraphGeneratorFin A 𝔥 j, hypergraphGeneratorFin_isHermitian A 𝔥 j⟩) =
      hypergraphGeneratorFin A 𝔥 j :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨hypergraphGeneratorFin A 𝔥 j, hypergraphGeneratorFin_isHermitian A 𝔥 j⟩

theorem ambientGeneratorFin_mixedGraph_reconstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [(v : V) → Fintype (A v)] [(v : V) → DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin (interactionCoordinateCount A G)) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨ambientGeneratorFin A G i, ambientGeneratorFin_isHermitian A G i⟩)
        (hermitianDirectedPart
          ⟨ambientGeneratorFin A G i, ambientGeneratorFin_isHermitian A G i⟩) =
      ambientGeneratorFin A G i :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨ambientGeneratorFin A G i, ambientGeneratorFin_isHermitian A G i⟩

theorem restrictedGeneratorFin_mixedGraph_reconstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [(v : V) → Fintype (A v)] [(v : V) → DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (i : Fin (interactionCoordinateCount A G)) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨restrictedGeneratorFin A G S i, restrictedGeneratorFin_isHermitian A G S i⟩)
        (hermitianDirectedPart
          ⟨restrictedGeneratorFin A G S i, restrictedGeneratorFin_isHermitian A G S i⟩) =
      restrictedGeneratorFin A G S i :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨restrictedGeneratorFin A G S i, restrictedGeneratorFin_isHermitian A G S i⟩

theorem hypergraphLocalGeneratorFin_mixedGraph_reconstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [(v : V) → Fintype (A v)]
    (𝔥 : Finset (Finset V))
    (i : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥))) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨hypergraphLocalGeneratorFin A 𝔥 i,
            hypergraphLocalGeneratorFin_isHermitian A 𝔥 i⟩)
        (hermitianDirectedPart
          ⟨hypergraphLocalGeneratorFin A 𝔥 i,
            hypergraphLocalGeneratorFin_isHermitian A 𝔥 i⟩) =
      hypergraphLocalGeneratorFin A 𝔥 i :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨hypergraphLocalGeneratorFin A 𝔥 i, hypergraphLocalGeneratorFin_isHermitian A 𝔥 i⟩

theorem finiteHankelMatrix_mixedGraph_reconstruction (m : ℕ → ℝ) (n : ℕ) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          (realHermitianComplexification ⟨finiteHankelMatrix m n, finiteHankelMatrix_isHermitian m n⟩))
        (hermitianDirectedPart
          (realHermitianComplexification ⟨finiteHankelMatrix m n, finiteHankelMatrix_isHermitian m n⟩)) =
      (finiteHankelMatrix m n).map Complex.ofReal :=
  realHermitianComplexification_reconstruct
    ⟨finiteHankelMatrix m n, finiteHankelMatrix_isHermitian m n⟩

theorem sharpTriangleAdjacency_mixedGraph_reconstruction :
    mixedHermitianMatrix
        (hermitianUndirectedPart (realHermitianComplexification
          ⟨StokesSpectralWitt.sharpTriangleAdjacency,
            StokesSpectralWitt.sharpTriangleAdjacency_isHermitian⟩))
        (hermitianDirectedPart (realHermitianComplexification
          ⟨StokesSpectralWitt.sharpTriangleAdjacency,
            StokesSpectralWitt.sharpTriangleAdjacency_isHermitian⟩)) =
      StokesSpectralWitt.sharpTriangleAdjacency.map Complex.ofReal :=
  realHermitianComplexification_reconstruct
    ⟨StokesSpectralWitt.sharpTriangleAdjacency,
      StokesSpectralWitt.sharpTriangleAdjacency_isHermitian⟩

theorem knobMatrix_mixedGraph_reconstruction
    {I : Type*} [Fintype I] [DecidableEq I]
    (A V : {M : Matrix I I ℝ // M.IsHermitian}) (g : ℝ) :
    mixedHermitianMatrix
        (hermitianUndirectedPart (realHermitianComplexification
          ⟨knobMatrix A.val V.val g, isHermitian_knobMatrix A.property V.property g⟩))
        (hermitianDirectedPart (realHermitianComplexification
          ⟨knobMatrix A.val V.val g, isHermitian_knobMatrix A.property V.property g⟩)) =
      (knobMatrix A.val V.val g).map Complex.ofReal :=
  realHermitianComplexification_reconstruct
    ⟨knobMatrix A.val V.val g, isHermitian_knobMatrix A.property V.property g⟩

end

end GaloisForLFunctions.HTGeometry.RandomMixedGraph

