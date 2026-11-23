import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.AngularBins

/-! # Finite Fourier tests for fixed-resolution angular counts -/
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section
private abbrev Angles := AddCircle (2*Real.pi)

/-- Finitely many small positive Fourier moments suffice for any
prescribed finite grid and count tolerance. -/
theorem finite_moments_control_grid (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ ∃ κ > 0, ∀ μ : ProbabilityMeasure Angles,
      (∀ j : ℕ, j < k → ‖∫ z, fourier ((j+1:ℕ):ℤ) z ∂(μ : Measure Angles)‖ < κ) →
      ∀ i : Fin (Q+1), |(μ : Measure Angles).real {z | turns z < i.val/(Q:ℝ)}-i.val/(Q:ℝ)| < δ := by
  classical
  let good (μ : ProbabilityMeasure Angles) := ∀ i : Fin (Q+1),
    |(μ : Measure Angles).real {z | turns z < i.val/(Q:ℝ)}-i.val/(Q:ℝ)| < δ
  let mom (μ : ProbabilityMeasure Angles) (j : ℕ) := ∫ z, fourier ((j+1:ℕ):ℤ) z ∂(μ : Measure Angles)
  by_contra h
  have bad (n : ℕ) : ∃ μ : ProbabilityMeasure Angles,
      (∀ j < n+1, ‖mom μ j‖ < 1/(n+1:ℕ)) ∧ ¬ good μ := by
    by_contra h'
    exact h ⟨n+1,Nat.succ_pos _,1/(n+1:ℕ),by positivity,fun μ hμ =>
      Classical.byContradiction (fun hb => h' ⟨μ,hμ,hb⟩)⟩
  choose μ hμ hb using bad
  have hconv := haar_of_positive_moments μ (fun j => Metric.tendsto_nhds.mpr (by
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
    filter_upwards [eventually_ge_atTop j,eventually_ge_atTop k] with n hj hn
    have hh : 1/((n+1:ℕ):ℝ) < ε := by
      have hh := (div_lt_iff₀ hε).mp (hk.trans_le (Nat.cast_le.mpr (show k ≤ n+1 by omega)))
      exact (div_lt_iff₀ (by positivity : 0 < ((n+1:ℕ):ℝ))).mpr (by rwa [mul_comm ε])
    rw [dist_zero_right]
    exact (hμ n j (by omega)).trans hh))
  have hgrid (i : Fin (Q+1)) : ∀ᶠ n : ℕ in atTop,
      |(μ n : Measure Angles).real {z | turns z < i.val/(Q:ℝ)}-i.val/(Q:ℝ)| < δ := by
    have hi : i.val/(Q:ℝ)∈Icc (0:ℝ) 1 :=
      ⟨by positivity,(div_le_one (Nat.cast_pos.mpr hQ)).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt))⟩
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (angular_count_of_haar μ hconv hi) δ hδ
  obtain ⟨n,hn⟩ := (eventually_all.mpr hgrid).exists
  exact hb n hn

#print axioms finite_moments_control_grid
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
