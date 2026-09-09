import GaloisForLFunctions.QuantumAlg.Primitives.QFT
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Finite Fourier spectral calculus for the critical Gibbs kernel derived from
arXiv:2609.00025, thermal prescription A. This connects the corpus QFT to
explicit diagonal weights; no spectral or invertibility assumption is exposed.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

noncomputable section

/-- A Fourier spectral multiplier using the corpus's normalized QFT. -/
def egbFixedChargeAQFTMultiplier (n : ℕ) (w : Fin (2 ^ n) → ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  QFTMatrix n * Matrix.diagonal w * star (QFTMatrix n)

/-- Every supplied weight is an exact diagonal entry in Fourier coordinates. -/
theorem egbFixedChargeAQFTMultiplier_diagonalization
    (n : ℕ) (w : Fin (2 ^ n) → ℂ) :
    star (QFTMatrix n) * egbFixedChargeAQFTMultiplier n w * QFTMatrix n =
      Matrix.diagonal w := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (QFT_mem_unitaryGroup n)
  simp only [egbFixedChargeAQFTMultiplier, Matrix.mul_assoc, h, Matrix.mul_one]
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

/-- Multiplication of these matrices is pointwise multiplication of their weights. -/
theorem egbFixedChargeAQFTMultiplier_mul
    (n : ℕ) (a b : Fin (2 ^ n) → ℂ) :
    egbFixedChargeAQFTMultiplier n a * egbFixedChargeAQFTMultiplier n b =
      egbFixedChargeAQFTMultiplier n (fun j => a j * b j) := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (QFT_mem_unitaryGroup n)
  simp only [egbFixedChargeAQFTMultiplier, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (QFTMatrix n)), h, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal a), Matrix.diagonal_mul_diagonal]

/-- Rank counts nonzero supplied Fourier weights, with QFT invertibility proved internally. -/
theorem egbFixedChargeAQFTMultiplier_rank
    (n : ℕ) (w : Fin (2 ^ n) → ℂ) :
    (egbFixedChargeAQFTMultiplier n w).rank = Fintype.card {j // w j ≠ 0} := by
  classical
  have hu := QFT_mem_unitaryGroup n
  have hs : star (QFTMatrix n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [star_star] using hu.1
  have hd := Matrix.UnitaryGroup.det_isUnit ⟨QFTMatrix n, hu⟩
  have hds := Matrix.UnitaryGroup.det_isUnit ⟨star (QFTMatrix n), hs⟩
  rw [egbFixedChargeAQFTMultiplier,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hds,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hd, Matrix.rank_diagonal]

/-- The multiplier is the weighted sum of actual QFT column projectors. -/
theorem egbFixedChargeAQFTMultiplier_entry
    (n : ℕ) (w : Fin (2 ^ n) → ℂ) (i j : Fin (2 ^ n)) :
    egbFixedChargeAQFTMultiplier n w i j =
      ∑ k : Fin (2 ^ n), w k * QFTMatrix n i k * star (QFTMatrix n j k) := by
  rw [egbFixedChargeAQFTMultiplier, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A single Fourier weight gives exactly the corresponding column projector. -/
theorem egbFixedChargeAQFTMultiplier_single_entry
    (n : ℕ) (r i j : Fin (2 ^ n)) (a : ℝ) :
    egbFixedChargeAQFTMultiplier n (Pi.single r (a : ℂ)) i j =
      (a : ℂ) * QFTMatrix n i r * star (QFTMatrix n j r) := by
  classical
  rw [egbFixedChargeAQFTMultiplier_entry]
  simp [Pi.single_apply]

end

end GaloisForLFunctions.HTGeometry
