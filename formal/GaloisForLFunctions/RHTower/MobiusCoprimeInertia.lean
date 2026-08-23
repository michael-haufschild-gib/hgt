import GaloisForLFunctions.HTGeometry.HermitianInertia
import GaloisForLFunctions.RHTower.MobiusCoprimeMatrixFactorization

open scoped ArithmeticFunction.Moebius

namespace RHTower

open Matrix Complex

noncomputable section

/-- Complexification of the finite integral coprimality matrix. -/
def finiteMobiusCoprimeMatrixComplex (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℂ :=
  (finiteMobiusCoprimeMatrix N).map (Int.castRingHom ℂ)

/-- Complexification of the finite integral divisor-incidence matrix. -/
def finiteMobiusDivisorIncidenceMatrixComplex (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℂ :=
  (finiteMobiusDivisorIncidenceMatrix N).map (Int.castRingHom ℂ)

/-- Complexification of the finite Möbius diagonal. -/
def finiteMobiusDiagonalMatrixComplex (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℂ :=
  (finiteMobiusDiagonalMatrix N).map (Int.castRingHom ℂ)

/-- The integral incidence factorization survives complexification exactly. -/
theorem finiteMobiusCoprimeMatrixComplex_factorization (N : ℕ) :
    finiteMobiusCoprimeMatrixComplex N = finiteMobiusDivisorIncidenceMatrixComplex N *
      finiteMobiusDiagonalMatrixComplex N *
        (finiteMobiusDivisorIncidenceMatrixComplex N).transpose := by
  have h := congrArg
    (fun M : Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℤ =>
      M.map (Int.castRingHom ℂ))
    (finiteMobiusCoprimeMatrix_factorization N)
  simpa only [finiteMobiusCoprimeMatrixComplex, finiteMobiusDivisorIncidenceMatrixComplex,
    finiteMobiusDiagonalMatrixComplex, Matrix.map_mul, Matrix.transpose_map] using h

/-- Complexified divisor incidence remains invertible. -/
theorem isUnit_finiteMobiusDivisorIncidenceMatrixComplex (N : ℕ) :
    IsUnit (finiteMobiusDivisorIncidenceMatrixComplex N) := by
  exact IsUnit.map (RingHom.mapMatrix (Int.castRingHom ℂ))
    (isUnit_finiteMobiusDivisorIncidenceMatrix N)

/-- Its transpose is the invertible congruence carrier. -/
theorem isUnit_finiteMobiusDivisorIncidenceMatrixComplex_transpose (N : ℕ) :
    IsUnit (finiteMobiusDivisorIncidenceMatrixComplex N).transpose :=
  (Matrix.isUnit_transpose _).mpr (isUnit_finiteMobiusDivisorIncidenceMatrixComplex N)

/-- Integer incidence entries are real, so transpose followed by conjugate transpose is identity. -/
theorem conjTranspose_transpose_finiteMobiusDivisorIncidenceMatrixComplex (N : ℕ) :
    ((finiteMobiusDivisorIncidenceMatrixComplex N).transpose)ᴴ =
      finiteMobiusDivisorIncidenceMatrixComplex N := by
  ext a d
  simp [finiteMobiusDivisorIncidenceMatrixComplex,
    finiteMobiusDivisorIncidenceMatrix, Matrix.conjTranspose]

/-- The complex coprimality matrix is an invertible congruence of the real Möbius diagonal. -/
theorem finiteMobiusCoprimeMatrixComplex_eq_congruence (N : ℕ) :
    finiteMobiusCoprimeMatrixComplex N =
      ((finiteMobiusDivisorIncidenceMatrixComplex N).transpose)ᴴ *
        finiteMobiusDiagonalMatrixComplex N *
          (finiteMobiusDivisorIncidenceMatrixComplex N).transpose := by
  rw [conjTranspose_transpose_finiteMobiusDivisorIncidenceMatrixComplex]
  exact finiteMobiusCoprimeMatrixComplex_factorization N

/-- The complex Möbius diagonal is Hermitian. -/
theorem finiteMobiusDiagonalMatrixComplex_isHermitian (N : ℕ) :
    (finiteMobiusDiagonalMatrixComplex N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  by_cases hab : a = b
  · subst b
    simp [finiteMobiusDiagonalMatrixComplex, finiteMobiusDiagonalMatrix]
  · simp [finiteMobiusDiagonalMatrixComplex, finiteMobiusDiagonalMatrix,
      hab, Ne.symm hab]

/-- The finite complex coprimality matrix is Hermitian. -/
theorem finiteMobiusCoprimeMatrixComplex_isHermitian (N : ℕ) :
    (finiteMobiusCoprimeMatrixComplex N).IsHermitian := by
  rw [finiteMobiusCoprimeMatrixComplex_eq_congruence]
  exact Matrix.isHermitian_conjTranspose_mul_mul _
    (finiteMobiusDiagonalMatrixComplex_isHermitian N)

/-- Exact negative inertia: one negative direction for every negative Möbius coordinate. -/
theorem hermNegIndex_finiteMobiusCoprimeMatrixComplex (N : ℕ) :
    GaloisForLFunctions.HTGeometry.hermNegIndex (finiteMobiusCoprimeMatrixComplex N) =
      ({d | μ d.1 = -1} : Finset (finiteMobiusCoprimeCoordinate N)).card := by
  calc
    GaloisForLFunctions.HTGeometry.hermNegIndex (finiteMobiusCoprimeMatrixComplex N) =
        GaloisForLFunctions.HTGeometry.hermNegIndex (finiteMobiusDiagonalMatrixComplex N) := by
      rw [finiteMobiusCoprimeMatrixComplex_eq_congruence]
      exact GaloisForLFunctions.HTGeometry.negIndex_conjugate _
        (isUnit_finiteMobiusDivisorIncidenceMatrixComplex_transpose N)
    _ = ({d | ((μ d.1 : ℤ) : ℝ) < 0} :
        Finset (finiteMobiusCoprimeCoordinate N)).card := by
      simpa [finiteMobiusDiagonalMatrixComplex, finiteMobiusDiagonalMatrix,
        Matrix.diagonal_map] using
        (GaloisForLFunctions.HTGeometry.negIndex_diagonal
          (fun d : finiteMobiusCoprimeCoordinate N => ((μ d.1 : ℤ) : ℝ)))
    _ = ({d | μ d.1 = -1} : Finset (finiteMobiusCoprimeCoordinate N)).card := by
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hneg
        have hnegZ : μ d.1 < (0 : ℤ) := by exact_mod_cast hneg
        rcases ArithmeticFunction.moebius_eq_or d.1 with hzero | hone | hnegone
        · omega
        · omega
        · exact hnegone
      · intro hnegone
        rw [hnegone]
        norm_num

/-- Exact positive inertia: one positive direction for every positive Möbius coordinate. -/
theorem hermPosIndex_finiteMobiusCoprimeMatrixComplex (N : ℕ) :
    GaloisForLFunctions.HTGeometry.hermPosIndex (finiteMobiusCoprimeMatrixComplex N) =
      ({d | μ d.1 = 1} : Finset (finiteMobiusCoprimeCoordinate N)).card := by
  calc
    GaloisForLFunctions.HTGeometry.hermPosIndex (finiteMobiusCoprimeMatrixComplex N) =
        GaloisForLFunctions.HTGeometry.hermPosIndex (finiteMobiusDiagonalMatrixComplex N) := by
      rw [finiteMobiusCoprimeMatrixComplex_eq_congruence]
      exact GaloisForLFunctions.HTGeometry.posIndex_conjugate _
        (isUnit_finiteMobiusDivisorIncidenceMatrixComplex_transpose N)
    _ = ({d | 0 < ((μ d.1 : ℤ) : ℝ)} :
        Finset (finiteMobiusCoprimeCoordinate N)).card := by
      simpa [finiteMobiusDiagonalMatrixComplex, finiteMobiusDiagonalMatrix,
        Matrix.diagonal_map] using
        (GaloisForLFunctions.HTGeometry.posIndex_diagonal
          (fun d : finiteMobiusCoprimeCoordinate N => ((μ d.1 : ℤ) : ℝ)))
    _ = ({d | μ d.1 = 1} : Finset (finiteMobiusCoprimeCoordinate N)).card := by
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hpos
        have hposZ : (0 : ℤ) < μ d.1 := by exact_mod_cast hpos
        rcases ArithmeticFunction.moebius_eq_or d.1 with hzero | hone | hnegone
        · omega
        · exact hone
        · omega
      · intro hone
        rw [hone]
        norm_num

/-- Exact nullity: one zero direction for every zero Möbius coordinate. -/
theorem hermNullIndex_finiteMobiusCoprimeMatrixComplex (N : ℕ) :
    GaloisForLFunctions.HTGeometry.hermNullIndex (finiteMobiusCoprimeMatrixComplex N) =
      ({d | μ d.1 = 0} : Finset (finiteMobiusCoprimeCoordinate N)).card := by
  calc
    GaloisForLFunctions.HTGeometry.hermNullIndex (finiteMobiusCoprimeMatrixComplex N) =
        GaloisForLFunctions.HTGeometry.hermNullIndex (finiteMobiusDiagonalMatrixComplex N) := by
      rw [finiteMobiusCoprimeMatrixComplex_eq_congruence]
      exact GaloisForLFunctions.HTGeometry.nullIndex_conjugate _
        (isUnit_finiteMobiusDivisorIncidenceMatrixComplex_transpose N)
    _ = ({d | ((μ d.1 : ℤ) : ℝ) = 0} :
        Finset (finiteMobiusCoprimeCoordinate N)).card := by
      simpa [finiteMobiusDiagonalMatrixComplex, finiteMobiusDiagonalMatrix,
        Matrix.diagonal_map] using
        (GaloisForLFunctions.HTGeometry.nullIndex_diagonal
          (fun d : finiteMobiusCoprimeCoordinate N => ((μ d.1 : ℤ) : ℝ)))
    _ = ({d | μ d.1 = 0} : Finset (finiteMobiusCoprimeCoordinate N)).card := by
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      norm_cast

end

end RHTower
