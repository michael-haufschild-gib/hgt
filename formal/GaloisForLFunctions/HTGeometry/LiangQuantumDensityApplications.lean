import GaloisForLFunctions.HTGeometry.LiangHermitianSpectralApplications
import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw
import GaloisForLFunctions.HTGeometry.PurityRankBarrier

/-!
# Liang curvature inequalities for finite quantum states

Applies the scalar-curvature spectral algebra to the corpus's bundled density matrices. Positivity
and trace-one normalization are fields of `DensityMatrix`, so every result below is a closed
statement about an arbitrary finite quantum state, with no additional analytic hypothesis.
-/

open scoped BigOperators ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Liang

theorem densityMatrix_trace_sq_le_one {d : ℕ} (ρ : _root_.RHTower.DensityMatrix d) :
    ((ρ.1 ^ 2).trace).re ≤ 1 := by
  have htrace : ρ.1.trace.re = 1 := by
    rw [ρ.property.2]
    norm_num
  calc
    ((ρ.1 ^ 2).trace).re ≤ ρ.1.trace.re ^ 2 :=
      posSemidef_trace_sq_le_sq_trace ρ.property.1
    _ = 1 := by rw [htrace]; norm_num

theorem densityMatrix_sqrt_trace_sq_le_one
    {d : ℕ} (ρ : _root_.RHTower.DensityMatrix d) :
    Real.sqrt ((ρ.1 ^ 2).trace).re ≤ 1 := by
  have htrace : ρ.1.trace.re = 1 := by
    rw [ρ.property.2]
    norm_num
  calc
    Real.sqrt ((ρ.1 ^ 2).trace).re ≤ ρ.1.trace.re :=
      posSemidef_sqrt_trace_sq_le_trace ρ.property.1
    _ = 1 := htrace

/-- For a density matrix, Liang's curvature commutator is the log-convexity inequality between
the second and third spectral moments. -/
theorem densityMatrix_sq_trace_sq_le_trace_cubic
    {d : ℕ} (ρ : _root_.RHTower.DensityMatrix d) :
    ((ρ.1 ^ 2).trace).re ^ 2 ≤ ((ρ.1 ^ 3).trace).re := by
  have hcomm := posSemidef_trace_cubic_commutator_nonneg ρ.property.1
  have htrace : ρ.1.trace.re = 1 := by
    rw [ρ.property.2]
    norm_num
  rw [htrace, one_mul] at hcomm
  linarith

theorem densityMatrix_cubic_purity_defect_eq_pairDifferenceEnergy
    {d : ℕ} (ρ : _root_.RHTower.DensityMatrix d) :
    ((ρ.1 ^ 3).trace).re - ((ρ.1 ^ 2).trace).re ^ 2 =
      pairDifferenceEnergy ρ.property.1.isHermitian.eigenvalues := by
  have hid := hermitian_curvatureCommutator_trace_identity ρ.property.1.isHermitian
  have htrace : ρ.1.trace.re = 1 := by
    rw [ρ.property.2]
    norm_num
  rw [htrace, one_mul] at hid
  exact hid

theorem densityMatrix_newton_weight_bound
    {d : ℕ} (ρ : _root_.RHTower.DensityMatrix d) (k : Fin d) :
    sigmaTwo ρ.property.1.isHermitian.eigenvalues ≤
      1 - ρ.property.1.isHermitian.eigenvalues k := by
  have htrace : ρ.1.trace.re = 1 := by
    rw [ρ.property.2]
    norm_num
  have h := hermitian_newton_weight_bound ρ.property.1.isHermitian k (by linarith)
  rw [htrace] at h
  simpa using h

theorem densityMatrix_purity_interval
    {d : ℕ} [Nonempty (Fin d)] (ρ : _root_.RHTower.DensityMatrix d) :
    1 / (d : ℝ) ≤ ((ρ.1 ^ 2).trace).re ∧ ((ρ.1 ^ 2).trace).re ≤ 1 := by
  have h₁ := sum_pow_eigenvalues_eq_trace_pow_re' ρ.property.1.isHermitian 1
  have hsum : ∑ i, ρ.property.1.isHermitian.eigenvalues i = 1 := by
    calc
      ∑ i, ρ.property.1.isHermitian.eigenvalues i = ρ.1.trace.re := by simpa using h₁
      _ = 1 := by rw [ρ.property.2]; norm_num
  constructor
  · calc
      1 / (d : ℝ) = 1 / (Fintype.card (Fin d) : ℝ) := by simp
      _ ≤ ∑ i, ρ.property.1.isHermitian.eigenvalues i ^ 2 :=
        inv_card_le_sum_sq _ hsum
      _ = ((ρ.1 ^ 2).trace).re :=
        sum_sq_eigenvalues_eq_trace_sq_re ρ.property.1.isHermitian
  · exact densityMatrix_trace_sq_le_one ρ

end GaloisForLFunctions.HTGeometry.Liang
