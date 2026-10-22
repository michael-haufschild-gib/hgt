import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDilationConservation
import Mathlib.Analysis.Matrix.PosDef

/-!
# Indefiniteness of the short reconstruction source matrix

At the square terminal scale with cutoff two, the last diagonal entry
of the actual doubled dilation source is zero and its mixed entry is
one. The determinant is therefore negative. Positivity for arbitrary
coefficient vectors cannot supply the signed estimate needed by the
short quadratic reconstruction.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

private theorem sum_one_two (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 2, f n) = f 1 + f 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
    Finset.Icc_self, Finset.sum_singleton]

private theorem source_zero : ccmPrimeDeficitDilationSource 0 = 0 := by
  simp [ccmPrimeDeficitDilationSource]

private theorem source_log_two : ccmPrimeDeficitDilationSource (Real.log 2) = 1 := by
  have he : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by positivity)
  rw [ccmPrimeDeficitDilationSource, he]
  have hf : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
  rw [hf, sum_one_two, sum_one_two]
  norm_num

private theorem double_source_zero :
    logarithmicDilationSum ccmPrimeDeficitDilationSource 0 = 0 := by
  simp [logarithmicDilationSum, logarithmicWeightedDilation, source_zero]

private theorem double_source_log_two :
    logarithmicDilationSum ccmPrimeDeficitDilationSource (Real.log 2) = 1 := by
  have he : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by positivity)
  unfold logarithmicDilationSum logarithmicWeightedDilation
  rw [he, show ⌊(2 : ℝ)⌋₊ = 2 from Nat.floor_natCast 2, sum_one_two]
  simp only [one_mul, Nat.cast_one, Nat.cast_ofNat, Real.log_one, sub_zero, sub_self,
    source_zero, source_log_two, add_zero]

/-- The actual source matrix on the two arithmetic indices at terminal
time `2 log 2`, when the short cutoff is exactly two. -/
def ccmPrimeDeficitShortSourceTwoPointMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => logarithmicDilationSum ccmPrimeDeficitDilationSource
    (2 * Real.log 2 - Real.log (((i.val + 1) * (j.val + 1) : ℕ) : ℝ))

theorem det_ccmPrimeDeficitShortSourceTwoPointMatrix :
    ccmPrimeDeficitShortSourceTwoPointMatrix.det = -1 := by
  norm_num only [Matrix.det_fin_two, ccmPrimeDeficitShortSourceTwoPointMatrix,
    Fin.val_zero, Fin.val_one, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, Nat.cast_one]
  have hl : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by ring, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hl, sub_self, double_source_zero, mul_zero,
    show 2 * Real.log 2 - Real.log 2 = Real.log 2 by ring, double_source_log_two]
  ring

/-- The actual source matrix is not positive semidefinite, independently
of any assertion about the value on the particular Möbius vector. -/
theorem ccmPrimeDeficitShortSourceTwoPointMatrix_not_posSemidef :
    ¬ ccmPrimeDeficitShortSourceTwoPointMatrix.PosSemidef := by
  intro h
  have hd := h.det_nonneg
  rw [det_ccmPrimeDeficitShortSourceTwoPointMatrix] at hd
  norm_num at hd

end RHTower
