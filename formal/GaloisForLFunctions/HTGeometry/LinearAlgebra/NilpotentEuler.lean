import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Trace duality and Euler operators for nilpotent matrices

The commutator equation `H*N - N*H = B` is solvable exactly when `B` is
trace-orthogonal to every matrix commuting with `N`. Nondegeneracy of the
matrix trace pairing identifies the commutator image with the double
orthogonal of its range.

If `N` is nilpotent, every commuting product `C*N` is nilpotent and has zero
trace. Hence an Euler operator `H` with `H*N - N*H = N` exists over every field.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The perfect bilinear pairing `tr(A*C)` on a finite matrix algebra. -/
def matrixTraceBilin : LinearMap.BilinForm K (Matrix ι ι K) :=
  (LinearMap.mul K (Matrix ι ι K)).compr₂ (Matrix.traceLinearMap ι K K)

/-- The trace pairing evaluates by matrix multiplication. -/
theorem matrixTraceBilin_apply (A C : Matrix ι ι K) :
    matrixTraceBilin A C = (A * C).trace := rfl

/-- Cyclicity of trace makes the matrix trace pairing symmetric. -/
theorem matrixTraceBilin_symm : (matrixTraceBilin (K := K) (ι := ι)).IsSymm :=
  ⟨fun A C => Matrix.trace_mul_comm A C⟩

/-- Matrix units recover every entry from the trace pairing. -/
theorem matrixTraceBilin_nondegenerate :
    (matrixTraceBilin (K := K) (ι := ι)).Nondegenerate := by
  constructor
  · intro A hA
    ext i j
    have h := hA (Matrix.single j i 1)
    simpa only [matrixTraceBilin_apply, Matrix.trace_mul_single,
      MulOpposite.op_one, one_smul, Matrix.zero_apply] using h
  · intro A hA
    ext i j
    have h := hA (Matrix.single j i 1)
    simpa only [matrixTraceBilin_apply, Matrix.trace_single_mul,
      one_smul, Matrix.zero_apply] using h

/-- Commutator with a fixed matrix on the right. -/
def matrixRightCommutator (N : Matrix ι ι K) : Module.End K (Matrix ι ι K) :=
  (LinearMap.mul K (Matrix ι ι K)).flip N - LinearMap.mul K (Matrix ι ι K) N

/-- The right commutator sends a candidate Euler operator to its defect. -/
theorem matrixRightCommutator_apply (N H : Matrix ι ι K) :
    matrixRightCommutator N H = H * N - N * H := rfl

omit [DecidableEq ι] in
/-- The trace adjoint of a right commutator is its negative. -/
theorem matrixTrace_commutator (N H C : Matrix ι ι K) :
    ((H * N - N * H) * C).trace = (H * (N * C - C * N)).trace := by
  rw [sub_mul, Matrix.trace_sub, mul_sub, Matrix.trace_sub, mul_assoc H N C]
  congr 1
  calc
    ((N * H) * C).trace = (N * (H * C)).trace := congrArg Matrix.trace (mul_assoc N H C)
    _ = ((H * C) * N).trace := Matrix.trace_mul_comm N (H * C)
    _ = (H * (C * N)).trace := congrArg Matrix.trace (mul_assoc H C N)

/-- The trace orthogonal of the commutator image is the centralizer. -/
theorem matrixTraceBilin_orthogonal_commutator_range (N : Matrix ι ι K) :
    matrixTraceBilin.orthogonal (LinearMap.range (matrixRightCommutator N)) =
      LinearMap.ker (matrixRightCommutator N) := by
  ext C
  constructor
  · intro hC
    have hz : ∀ H, matrixTraceBilin H (N * C - C * N) = 0 := by
      intro H
      rw [matrixTraceBilin_apply, ← matrixTrace_commutator]
      exact hC _ ⟨H, rfl⟩
    have hc := matrixTraceBilin_nondegenerate.2 _ hz
    apply LinearMap.mem_ker.mpr
    change C * N - N * C = 0
    rw [sub_eq_zero.mp hc, sub_self]
  · intro hC H hH
    obtain ⟨X, rfl⟩ := hH
    have hc : C * N = N * C := sub_eq_zero.mp (LinearMap.mem_ker.mp hC)
    change ((X * N - N * X) * C).trace = 0
    rw [matrixTrace_commutator, ← hc, sub_self, mul_zero, Matrix.trace_zero]

/-- Exact obstruction to solving an inhomogeneous matrix commutator equation. -/
theorem matrix_commutator_solvable_iff (N B : Matrix ι ι K) :
    (∃ H : Matrix ι ι K, H * N - N * H = B) ↔
      ∀ C : Matrix ι ι K, Commute C N → (C * B).trace = 0 := by
  change B ∈ LinearMap.range (matrixRightCommutator N) ↔ _
  rw [← LinearMap.BilinForm.orthogonal_orthogonal matrixTraceBilin_nondegenerate
      matrixTraceBilin_symm.isRefl (LinearMap.range (matrixRightCommutator N)),
    matrixTraceBilin_orthogonal_commutator_range]
  constructor
  · intro h C hc
    exact h C (LinearMap.mem_ker.mpr (sub_eq_zero.mpr hc))
  · intro h C hc
    exact h C (sub_eq_zero.mp (LinearMap.mem_ker.mp hc))

/-- Every finite nilpotent matrix admits an Euler operator in every characteristic. -/
theorem exists_matrixEuler_of_isNilpotent (N : Matrix ι ι K) (hN : IsNilpotent N) :
    ∃ H : Matrix ι ι K, H * N - N * H = N := by
  apply (matrix_commutator_solvable_iff N N).mpr
  intro C hc
  have hCN : IsNilpotent (C * N) := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [hc.mul_pow, hk, mul_zero]⟩
  exact isNilpotent_iff_eq_zero.mp (Matrix.isNilpotent_trace_of_isNilpotent hCN)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.matrix_commutator_solvable_iff
#print axioms GaloisForLFunctions.HTGeometry.exists_matrixEuler_of_isNilpotent
