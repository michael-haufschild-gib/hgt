import GaloisForLFunctions.RHTower.MobiusCoprimeMatrixFactorization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace RHTower

noncomputable section

/-- Real divisor-incidence matrix on the positive coordinates through `N`. -/
def finiteDivisorIncidenceMatrixReal (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℝ :=
  (finiteMobiusDivisorIncidenceMatrix N).map (Int.castRingHom ℝ)

/-- Diagonal matrix of a real arithmetic coefficient sequence on `1,...,N`. -/
def finiteDivisorStationaryDiagonal (c : ℕ → ℝ) (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℝ :=
  Matrix.diagonal fun d => c d.1

/-- Finite divisor-stationary kernel `sum_{d | gcd(a,b)} c(d)`. -/
def finiteDivisorStationaryKernel (c : ℕ → ℝ) (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℝ :=
  fun a b => ∑ d ∈ Finset.Icc 1 N, if d ∣ a.1 ∧ d ∣ b.1 then c d else 0

/-- Exact finite incidence factorization of every divisor-stationary kernel. -/
theorem finiteDivisorStationaryKernel_factorization (c : ℕ → ℝ) (N : ℕ) :
    finiteDivisorStationaryKernel c N =
      finiteDivisorIncidenceMatrixReal N * finiteDivisorStationaryDiagonal c N *
        (finiteDivisorIncidenceMatrixReal N).transpose := by
  ext a b
  unfold finiteDivisorStationaryKernel
  rw [Matrix.mul_apply]
  simp only [finiteDivisorIncidenceMatrixReal, finiteMobiusDivisorIncidenceMatrix,
    finiteDivisorStationaryDiagonal, Matrix.map_apply, Matrix.mul_diagonal,
    Matrix.transpose_apply]
  rw [Finset.sum_subtype (Finset.Icc 1 N) (by intro x; rfl)]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hda hdb <;> simp_all

/-- Real divisor incidence remains invertible. -/
theorem isUnit_finiteDivisorIncidenceMatrixReal (N : ℕ) :
    IsUnit (finiteDivisorIncidenceMatrixReal N) := by
  exact IsUnit.map (RingHom.mapMatrix (Int.castRingHom ℝ))
    (isUnit_finiteMobiusDivisorIncidenceMatrix N)

/-- The transpose of real divisor incidence is the invertible congruence carrier. -/
theorem isUnit_finiteDivisorIncidenceMatrixReal_transpose (N : ℕ) :
    IsUnit (finiteDivisorIncidenceMatrixReal N).transpose :=
  (Matrix.isUnit_transpose _).mpr (isUnit_finiteDivisorIncidenceMatrixReal N)

/-- Fixed-cutoff positivity is exactly nonnegativity of every visible divisor coefficient. -/
theorem finiteDivisorStationaryKernel_posSemidef_iff (c : ℕ → ℝ) (N : ℕ) :
    (finiteDivisorStationaryKernel c N).PosSemidef ↔
      ∀ d : finiteMobiusCoprimeCoordinate N, 0 ≤ c d.1 := by
  rw [finiteDivisorStationaryKernel_factorization]
  have hcongruence :
      (finiteDivisorIncidenceMatrixReal N * finiteDivisorStationaryDiagonal c N *
          (finiteDivisorIncidenceMatrixReal N).transpose).PosSemidef ↔
        (finiteDivisorStationaryDiagonal c N).PosSemidef := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] using
      (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
        (x := finiteDivisorStationaryDiagonal c N)
        (isUnit_finiteDivisorIncidenceMatrixReal_transpose N))
  rw [hcongruence, finiteDivisorStationaryDiagonal, Matrix.posSemidef_diagonal_iff]

/-- All finite divisor-stationary matrices are positive semidefinite exactly when every positive
arithmetic coefficient is nonnegative. -/
theorem forall_finiteDivisorStationaryKernel_posSemidef_iff (c : ℕ → ℝ) :
    (∀ N : ℕ, (finiteDivisorStationaryKernel c N).PosSemidef) ↔
      ∀ d : ℕ, 0 < d → 0 ≤ c d := by
  constructor
  · intro h d hd
    have hN := (finiteDivisorStationaryKernel_posSemidef_iff c d).mp (h d)
    exact hN ⟨d, Finset.mem_Icc.mpr ⟨hd, le_rfl⟩⟩
  · intro h N
    rw [finiteDivisorStationaryKernel_posSemidef_iff]
    intro d
    exact h d.1 (Finset.mem_Icc.mp d.2).1

end

end RHTower
