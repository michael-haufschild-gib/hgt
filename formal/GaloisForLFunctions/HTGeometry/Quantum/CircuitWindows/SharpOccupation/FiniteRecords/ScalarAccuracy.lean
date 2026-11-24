import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.ScalarScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.ScalarWindows

/-! # Relative Haar accuracy for rare scalar visits in finite physical records -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- All windows of length D times the fine recurrence deadline recover
the exact Haar mass within relative error 4/D. The same estimate holds
for moving angular tolerances down to D² times the recurrence precision. -/
theorem gaussian_finite_scalar_relative_accuracy :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D : ℕ := 2^N
      let δ := 1/(2:ℝ)^D
      let G := (2:ℝ)^(D^c)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ x : ℝ, (D:ℝ)^2*δ ≤ x → x+δ ≤ 1/2 → ∀ a T : ℝ, D*G ≤ T →
        |visitFraction H 0 (zeroGateArcTolerance x) a (a+T)/zeroGateArcDensity D x-1| ≤ 4/D := by
  obtain ⟨c,h⟩ := SpectralJets.HighPrecision.gaussian_fine_scalar_windows
  refine ⟨c,?_⟩
  filter_upwards [h,gaussian_path_all_prefixes_maximally_projective] with ω hclock hmax
  filter_upwards [hclock] with k hc
  intro N D δ G H x hlo hhi a T hT
  have hD : (2:ℝ) ≤ D := by
    exact_mod_cast (show 2^1 ≤ 2^N from Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
  exact scalar_accuracy_at_scale H (hmax k) (show 0 < 1/(2:ℝ)^D by positivity) (show 0 < (2:ℝ)^(D^c) by positivity)
    hc a T hD hlo hhi hT

#print axioms gaussian_finite_scalar_relative_accuracy
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
