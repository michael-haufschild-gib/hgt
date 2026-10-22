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

/-!
# Mixed-graph decomposition of concrete Hermitian matrix families

Every complex Hermitian matrix `H` is reconstructed as `U + i D` from its undirected part
`U = Re H` (real symmetric) and directed part `D = Im H` (real skew-symmetric), so it is the
Hermitian adjacency matrix of a weighted mixed graph. This module specializes that identity to
the Hermitian families used elsewhere in the corpus: graph-local edge commutator matrices, Pauli
strings on a finite qubit register, nearest-neighbour chain Pauli generators, hypergraph and
interaction-coordinate generators, and (after complexification, with zero directed part) real
finite Hankel blocks, the sharp-triangle adjacency matrix and the affine knob family `A + g V`.

## Main results

- `graphLocalEdgeMatrix_mixedGraph_reconstruction`, `finitePauliMatrix_mixedGraph_reconstruction`,
  `chainPauliFin_mixedGraph_reconstruction`: these complex Hermitian matrices equal
  `Re H + i Im H` in mixed-graph form.
- `hypergraphGeneratorFin_mixedGraph_reconstruction`, `ambientGeneratorFin_mixedGraph_reconstruction`,
  `restrictedGeneratorFin_mixedGraph_reconstruction`,
  `hypergraphLocalGeneratorFin_mixedGraph_reconstruction`: the same for the canonical Hermitian
  generators of hypergraph, interaction and subsystem coordinates.
- `finiteHankelMatrix_mixedGraph_reconstruction`, `sharpTriangleAdjacency_mixedGraph_reconstruction`,
  `knobMatrix_mixedGraph_reconstruction`: complexified real symmetric matrices are mixed-graph
  matrices.

## Hypotheses

All results are unconditional. In `knobMatrix_mixedGraph_reconstruction` the matrices `A` and `V`
are supplied as real symmetric (Hermitian) matrices, which is the typing of the family.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

/-- A graph-local edge commutator matrix equals `U + i D` built from its real symmetric and real
skew-symmetric parts. -/
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

/-- A Pauli string on a finite qubit register is a mixed-graph Hermitian matrix `Re P + i Im P`. -/
theorem finitePauliMatrix_mixedGraph_reconstruction
    {σ : Type*} [Fintype σ] [DecidableEq σ] (P : σ → Option (Fin 3)) :
    mixedHermitianMatrix
        (hermitianUndirectedPart ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩)
        (hermitianDirectedPart ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩) =
      finitePauliMatrix P :=
  mixedHermitianMatrix_parts_reconstruct ⟨finitePauliMatrix P, finitePauliMatrix_isHermitian P⟩

/-- Each numbered nearest-neighbour chain Pauli generator is a mixed-graph Hermitian matrix. -/
theorem chainPauliFin_mixedGraph_reconstruction
    (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) :
    mixedHermitianMatrix
        (hermitianUndirectedPart ⟨chainPauliFin n a, chainPauliFin_isHermitian n a⟩)
        (hermitianDirectedPart ⟨chainPauliFin n a, chainPauliFin_isHermitian n a⟩) =
      chainPauliFin n a :=
  mixedHermitianMatrix_parts_reconstruct ⟨chainPauliFin n a, chainPauliFin_isHermitian n a⟩

/-- Each canonical hypergraph coordinate generator is a mixed-graph Hermitian matrix. -/
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

/-- Each ambient interaction-coordinate generator of a site-factor graph is a mixed-graph
Hermitian matrix. -/
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

/-- Each subsystem-restricted interaction generator on a site set `S` is a mixed-graph Hermitian
matrix. -/
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

/-- Each canonical Hermitian basis generator of the hyperedge-local space is a mixed-graph
Hermitian matrix. -/
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

/-- The complexified finite Hankel block `(m (i + j))` is a mixed-graph matrix with zero
directed part. -/
theorem finiteHankelMatrix_mixedGraph_reconstruction (m : ℕ → ℝ) (n : ℕ) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          (realHermitianComplexification ⟨finiteHankelMatrix m n, finiteHankelMatrix_isHermitian m n⟩))
        (hermitianDirectedPart
          (realHermitianComplexification ⟨finiteHankelMatrix m n, finiteHankelMatrix_isHermitian m n⟩)) =
      (finiteHankelMatrix m n).map Complex.ofReal :=
  realHermitianComplexification_reconstruct
    ⟨finiteHankelMatrix m n, finiteHankelMatrix_isHermitian m n⟩

/-- The complexified sharp-triangle adjacency matrix (weights 6, 4, 3) is a mixed-graph matrix. -/
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

/-- For real symmetric `A`, `V` and real `g`, the complexified knob matrix `A + g V` is a
mixed-graph matrix. -/
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

