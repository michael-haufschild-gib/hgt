import GaloisForLFunctions.QuantumAlg.Primitives.WalshHadamard
import GaloisForLFunctions.HTGeometry.LpTwoCurry
import GaloisForLFunctions.HTGeometry.ConstitutiveDependentLpGaugeTransport
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Walsh cancellation on infinitely many finite Hilbert blocks

The existing quantum Walsh matrix gives an exact isometry on each finite
`ℓ²` block. Regrouping coordinates extends it to arbitrary many blocks.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open QuantumAlg.WalshHadamard

/-- The already proved finite Walsh unitary, acting on `lp` coordinates. -/
def walshLpIsometry (k : ℕ) :
    lp (fun _ : Fin (2 ^ k) => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Fin (2 ^ k) => ℂ) 2 :=
  (lpPiLpₗᵢ (fun _ : Fin (2 ^ k) => ℂ) ℂ).trans
    ((Unitary.linearIsometryEquiv
      (H := EuclideanSpace ℂ (Fin (2 ^ k)))
      ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ k)) (hadamardLayerOp k),
      Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ k)))
        (hadamardLayerOp_mem_unitaryGroup k)⟩).trans
      (lpPiLpₗᵢ (fun _ : Fin (2 ^ k) => ℂ) ℂ).symm)

theorem walshLpIsometry_apply (k : ℕ) (f : lp (fun _ : Fin (2 ^ k) => ℂ) 2)
    (r : Fin (2 ^ k)) :
    walshLpIsometry k f r = ∑ s, invSqrtCard k * walshSign r s * f s := rfl

/-- Arbitrarily many Walsh blocks preserve the entire infinite `ℓ²` norm. -/
def walshBlockIsometry (I : Type*) (k : ℕ) :
    lp (fun _ : I × Fin (2 ^ k) => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : I × Fin (2 ^ k) => ℂ) 2 :=
  lpTwoCurry.trans ((lpFamilyIsometryEquiv (by norm_num)
    (fun _ : I => walshLpIsometry k)).trans lpTwoCurry.symm)

theorem walshBlockIsometry_apply {I : Type*} (k : ℕ)
    (f : lp (fun _ : I × Fin (2 ^ k) => ℂ) 2) (m : I) (r : Fin (2 ^ k)) :
    walshBlockIsometry I k f (m, r) = ∑ s, invSqrtCard k * walshSign r s * f (m, s) := rfl

/-- Removing the normalization recovers the literal sign matrix. -/
theorem sqrt_mul_walshBlockIsometry_apply {I : Type*} (k : ℕ)
    (f : lp (fun _ : I × Fin (2 ^ k) => ℂ) 2) (m : I) (r : Fin (2 ^ k)) :
    (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) * walshBlockIsometry I k f (m, r) =
      ∑ s, walshSign r s * f (m, s) := by
  rw [walshBlockIsometry_apply, Finset.mul_sum]
  have hs : (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < (2 ^ k : ℕ))))
  apply Finset.sum_congr rfl
  intro s _
  simp only [invSqrtCard]
  field_simp

end
end GaloisForLFunctions.HTGeometry
