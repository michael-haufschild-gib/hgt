import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.RHTower.SuzukiOnePrimeTerminalSimilarityTransport
import GaloisForLFunctions.RHTower.MobiusCoprimeInertia

namespace GaloisForLFunctions.RHTower.RandomMixedGraph

open GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

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

