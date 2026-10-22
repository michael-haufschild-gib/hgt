import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOnePrimeTerminalSimilarityTransport
import GaloisForLFunctions.RHTower.MobiusCoprimeInertia

/-!
# Mixed-graph decompositions of arithmetic Hermitian matrices

Every complex Hermitian matrix `H` decomposes as `H = U + i D` with `U = Re H` real symmetric (the
undirected part) and `D = Im H` real skew-symmetric (the directed part), as in the Hermitian
adjacency model of mixed graphs. This module instantiates the reconstruction identity for three
concrete Hermitian matrices: the `2 × 2` swap matrix similar to the one-prime terminal adjacency,
and the complexified finite Möbius diagonal and coprimality matrices of size `N`.

## Main results

- `onePrimeTerminalSymmetricAdjacency_mixedGraph_reconstruction`: the swap matrix equals the mixed
  Hermitian matrix of its undirected and directed parts.
- `finiteMobiusDiagonalMatrixComplex_mixedGraph_reconstruction`: the same for the finite Möbius
  diagonal matrix.
- `finiteMobiusCoprimeMatrixComplex_mixedGraph_reconstruction`: the same for the finite coprimality
  matrix.

## Hypotheses

All results are unconditional identities of matrices.
-/

namespace GaloisForLFunctions.RHTower.RandomMixedGraph

open GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

/-- The Hermitian `2 × 2` swap matrix similar to the one-prime terminal adjacency is recovered as
`U + i D` from its real symmetric and real skew-symmetric parts. -/
theorem onePrimeTerminalSymmetricAdjacency_mixedGraph_reconstruction :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨_root_.RHTower.onePrimeTerminalSymmetricAdjacency,
            _root_.RHTower.onePrimeTerminalSymmetricAdjacency_isHermitian⟩)
        (hermitianDirectedPart
          ⟨_root_.RHTower.onePrimeTerminalSymmetricAdjacency,
            _root_.RHTower.onePrimeTerminalSymmetricAdjacency_isHermitian⟩) =
      _root_.RHTower.onePrimeTerminalSymmetricAdjacency :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨_root_.RHTower.onePrimeTerminalSymmetricAdjacency,
      _root_.RHTower.onePrimeTerminalSymmetricAdjacency_isHermitian⟩

/-- The complexified finite Möbius diagonal matrix is recovered as `U + i D` from its undirected and
directed parts. -/
theorem finiteMobiusDiagonalMatrixComplex_mixedGraph_reconstruction (N : ℕ) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨_root_.RHTower.finiteMobiusDiagonalMatrixComplex N,
            _root_.RHTower.finiteMobiusDiagonalMatrixComplex_isHermitian N⟩)
        (hermitianDirectedPart
          ⟨_root_.RHTower.finiteMobiusDiagonalMatrixComplex N,
            _root_.RHTower.finiteMobiusDiagonalMatrixComplex_isHermitian N⟩) =
      _root_.RHTower.finiteMobiusDiagonalMatrixComplex N :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨_root_.RHTower.finiteMobiusDiagonalMatrixComplex N,
      _root_.RHTower.finiteMobiusDiagonalMatrixComplex_isHermitian N⟩

/-- The complexified finite coprimality matrix is recovered as `U + i D` from its undirected and
directed parts. -/
theorem finiteMobiusCoprimeMatrixComplex_mixedGraph_reconstruction (N : ℕ) :
    mixedHermitianMatrix
        (hermitianUndirectedPart
          ⟨_root_.RHTower.finiteMobiusCoprimeMatrixComplex N,
            _root_.RHTower.finiteMobiusCoprimeMatrixComplex_isHermitian N⟩)
        (hermitianDirectedPart
          ⟨_root_.RHTower.finiteMobiusCoprimeMatrixComplex N,
            _root_.RHTower.finiteMobiusCoprimeMatrixComplex_isHermitian N⟩) =
      _root_.RHTower.finiteMobiusCoprimeMatrixComplex N :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨_root_.RHTower.finiteMobiusCoprimeMatrixComplex N,
      _root_.RHTower.finiteMobiusCoprimeMatrixComplex_isHermitian N⟩

end

end GaloisForLFunctions.RHTower.RandomMixedGraph

