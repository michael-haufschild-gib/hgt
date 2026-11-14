import GaloisForLFunctions.HTGeometry.TaylorJordanNormalization
import GaloisForLFunctions.HTGeometry.LinearAlgebra.FramedTruncatedResolution

/-!
# Periodic exactness for derivative jets and metric Jordan chains

Factorial normalization identifies derivative jets with the regular truncated
polynomial module. The nilpotent Jordan chain and its highest power therefore
form an exact pair, both in raw derivative coordinates and in the reversed
metric coordinates.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ABHN Matrix Polynomial

private theorem transpose_metricJordanBlock_zero_eq_toeplitz (d : ℕ) :
    (metricJordanBlock d (0 : ℂ)).transpose = toeplitz d (X : ℂ[X]) := by
  ext i j
  by_cases h : j.val + 1 = i.val
  · have hne : j ≠ i := by intro he; subst i; omega
    have hle : j.val ≤ i.val := by omega
    have hsub : i.val - j.val = 1 := by omega
    simp [metricJordanBlock, toeplitz_apply, hne, h, hle, hsub]
  · by_cases hle : j.val ≤ i.val
    · have hsub : 1 ≠ i.val - j.val := by omega
      simp [metricJordanBlock, toeplitz_apply, Polynomial.coeff_X, h, hle, hsub]
    · simp [metricJordanBlock, toeplitz_apply, h, hle]

theorem factorialTaylorFrame_cyclic_conjugate (n : ℕ) :
    (factorialTaylorFrame (n + 1)).val * derivativeJordanBlock (n + 1) 0 *
        (factorialTaylorFrame (n + 1)).inv = cyclicCompanionMatrix n (0 : ℂ) := by
  rw [factorialTaylorFrame_conjugate, transpose_metricJordanBlock_zero_eq_toeplitz,
    cyclicCompanionMatrix_zero_eq_toeplitz]

theorem derivativeJordanBlock_zero_eq_framedShift (n : ℕ) :
    derivativeJordanBlock (n + 1) 0 = framedCyclicShift n (factorialTaylorFrame (n + 1)) := by
  rw [framedCyclicShift, ← factorialTaylorFrame_cyclic_conjugate]
  let P := factorialTaylorFrame (n + 1)
  calc
    derivativeJordanBlock (n + 1) 0 = (P.inv * P.val) *
        derivativeJordanBlock (n + 1) 0 * (P.inv * P.val) := by rw [P.inv_val]; simp
    _ = _ := by simp only [P, mul_assoc]

/-- The derivative-jet shift and its top power are mutually exact. -/
theorem derivativeJordanBlock_zero_periodic_exact (n : ℕ) :
    LinearMap.range (derivativeJordanBlock (n + 1) 0).mulVecLin =
        LinearMap.ker (derivativeJordanBlock (n + 1) 0 ^ n).mulVecLin ∧
      LinearMap.range (derivativeJordanBlock (n + 1) 0 ^ n).mulVecLin =
        LinearMap.ker (derivativeJordanBlock (n + 1) 0).mulVecLin := by
  rw [derivativeJordanBlock_zero_eq_framedShift]
  exact framedCyclicShift_periodic_exact n _

/-- The reversal frame sends the lower shift to the metric upper shift. -/
theorem metricJordanShift_eq_framedShift (n : ℕ) :
    metricJordanShift n = framedCyclicShift n
      (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) := by
  rw [framedCyclicShift, cyclicCompanionMatrix_zero_eq_toeplitz,
    ← transpose_metricJordanBlock_zero_eq_toeplitz]
  have hinv : (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin (n + 1)))).inv =
      (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin (n + 1)))).val := by
    change (Fin.revPerm⁻¹).permMatrix ℂ = Fin.revPerm.permMatrix ℂ
    rfl
  rw [hinv]
  have hconj := reversal_conjugate_transpose_jordan (n + 1) (0 : ℂ)
  rw [hinv] at hconj
  rw [hconj]
  ext i j
  by_cases h : i = j
  · subst j
    simp [metricJordanShift, metricJordanBlock]
  · simp [metricJordanShift, metricJordanBlock, h]

/-- The metric Jordan chain has the same two-periodic exactness as the polynomial quotient. -/
theorem metricJordanShift_periodic_exact (n : ℕ) :
    LinearMap.range (metricJordanShift n).mulVecLin =
        LinearMap.ker (metricJordanShift n ^ n).mulVecLin ∧
      LinearMap.range (metricJordanShift n ^ n).mulVecLin =
        LinearMap.ker (metricJordanShift n).mulVecLin := by
  rw [metricJordanShift_eq_framedShift]
  exact framedCyclicShift_periodic_exact n _

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.derivativeJordanBlock_zero_periodic_exact
#print axioms GaloisForLFunctions.HTGeometry.metricJordanShift_periodic_exact
