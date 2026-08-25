import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Determinant of a finite self-adjoint unitary exponential

For a finite complex self-adjoint matrix `H`, the determinant of `exp(iH)` is exactly
`exp(i trace(H))`. The proof diagonalizes `H`, evaluates the matrix exponential on the diagonal,
and cancels the determinant of the conjugating unitary with its adjoint.
-/

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

theorem isHermitian_trace_eq_sum_eigenvalues
    {H : Matrix iota iota ℂ} (hHerm : H.IsHermitian) :
    Matrix.trace H = ∑ i, (hHerm.eigenvalues i : ℂ) := by
  let V : Matrix iota iota ℂ := hHerm.eigenvectorUnitary
  let D : Matrix iota iota ℂ :=
    Matrix.diagonal (fun i ↦ (hHerm.eigenvalues i : ℂ))
  have hspec : H = V * D * star V := by
    have h := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hV : star V * V = 1 := hHerm.eigenvectorUnitary.2.1
  calc
    Matrix.trace H = Matrix.trace (V * D * star V) := congrArg Matrix.trace hspec
    _ = Matrix.trace (V * (D * star V)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace ((D * star V) * V) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace D := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
    _ = ∑ i, (hHerm.eigenvalues i : ℂ) := by simp [D]

theorem det_expUnitary_eq_exp_I_mul_trace
    (H : selfAdjoint (Matrix iota iota ℂ)) :
    ((selfAdjoint.expUnitary H : Matrix iota iota ℂ).det) =
      Complex.exp (Complex.I * Matrix.trace (H : Matrix iota iota ℂ)) := by
  have hHerm : (H : Matrix iota iota ℂ).IsHermitian := H.2
  let V : Matrix iota iota ℂ := hHerm.eigenvectorUnitary
  let D : Matrix iota iota ℂ :=
    Matrix.diagonal (fun i ↦ (Complex.I * hHerm.eigenvalues i : ℂ))
  have hVunitary : V ∈ unitary (Matrix iota iota ℂ) := hHerm.eigenvectorUnitary.2
  have hVinv : V⁻¹ = star V :=
    Matrix.inv_eq_left_inv (Unitary.mem_iff.mp hVunitary).1
  have hVunit : IsUnit V :=
    ⟨⟨V, star V, (Unitary.mem_iff.mp hVunitary).2,
      (Unitary.mem_iff.mp hVunitary).1⟩, rfl⟩
  have hspec : (H : Matrix iota iota ℂ) =
      V * Matrix.diagonal (fun i ↦ (hHerm.eigenvalues i : ℂ)) * star V := by
    have h := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hsmul : Complex.I • (H : Matrix iota iota ℂ) = V * D * star V := by
    rw [hspec]
    calc
      Complex.I •
          (V * Matrix.diagonal (fun i ↦ (hHerm.eigenvalues i : ℂ)) * star V) =
        (Complex.I •
          (V * Matrix.diagonal (fun i ↦ (hHerm.eigenvalues i : ℂ)))) * star V := by
            rw [smul_mul_assoc]
      _ = (V * (Complex.I •
          Matrix.diagonal (fun i ↦ (hHerm.eigenvalues i : ℂ)))) * star V := by
            rw [mul_smul_comm]
      _ = V * D * star V := by
            congr 1
            ext i j
            simp [D]
            ring
  have hexp : NormedSpace.exp (Complex.I • (H : Matrix iota iota ℂ)) =
      V * Matrix.diagonal
        (fun i ↦ Complex.exp (Complex.I * hHerm.eigenvalues i)) * star V := by
    have hfun : NormedSpace.exp
        (fun i ↦ (Complex.I * hHerm.eigenvalues i : ℂ)) =
        fun i ↦ Complex.exp (Complex.I * hHerm.eigenvalues i) := by
      funext i
      rw [Pi.coe_exp]
      exact (congrFun Complex.exp_eq_exp_ℂ _).symm
    rw [hsmul, ← hVinv, Matrix.exp_conj _ _ hVunit, Matrix.exp_diagonal]
    rw [hfun]
  rw [selfAdjoint.expUnitary_coe, hexp]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hdetV : V.det * (star V).det = 1 := by
    rw [← Matrix.det_mul, (Unitary.mem_iff.mp hVunitary).2, Matrix.det_one]
  calc
    (V.det * (∏ i, Complex.exp (Complex.I * hHerm.eigenvalues i))) * (star V).det =
        (V.det * (star V).det) *
          (∏ i, Complex.exp (Complex.I * hHerm.eigenvalues i)) := by ring
    _ = ∏ i, Complex.exp (Complex.I * hHerm.eigenvalues i) := by rw [hdetV, one_mul]
    _ = Complex.exp (Complex.I * Matrix.trace (H : Matrix iota iota ℂ)) := by
      rw [isHermitian_trace_eq_sum_eigenvalues hHerm]
      have hexpSum := map_prod Complex.expMonoidHom
        (fun i ↦ Multiplicative.ofAdd
          (Complex.I * (hHerm.eigenvalues i : ℂ))) Finset.univ
      rw [show Complex.I * ∑ i, (hHerm.eigenvalues i : ℂ) =
          ∑ i, Complex.I * (hHerm.eigenvalues i : ℂ) by
            rw [Finset.mul_sum]]
      exact hexpSum.symm

end

end GaloisForLFunctions.HTGeometry
