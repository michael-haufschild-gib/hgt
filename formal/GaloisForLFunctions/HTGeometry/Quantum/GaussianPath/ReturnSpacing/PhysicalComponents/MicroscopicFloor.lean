import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.AngularProfile

/-! # Fixed-error exclusion after nine tenths of a spectral turn -/
open Matrix Real Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Past nine tenths of a turn, two opposite product probes exclude
a scalar at error 1/5 until any given inverse-volume deadline. -/
theorem gaussian_microscopic_scalar_floor (B : ℝ) (hB : 0<B) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
      ∀ t : ℝ, 0<t → t≤B/N → 9*π/5 ≤ t*circuitHamiltonianSpectralWidth H →
        1/5 < orbitCircuitDistance H 0 t := by
  have hsin : 3/14 ≤ sin (π/14) := by
    have h := QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le (A:=π/6) (x:=π/14)
      (by positivity) (by linarith only [pi_pos]) (by positivity) (by linarith only [pi_pos])
    rw [sin_pi_div_six] at h
    exact (show (3/14:ℝ)=(1/2/(π/6))*(π/14) by field_simp [pi_ne_zero]; ring).le.trans h
  filter_upwards [gaussian_chord_from_width B hB] with ω hh
  filter_upwards [hh] with n hn
  intro N u H t ht hshort hlate
  have h := hn t ht hshort (π/7) (by positivity) (by linarith only [pi_pos]) (by linarith only [hlate,pi_pos])
  rw [show π/7/2=π/14 by ring] at h
  linarith only [hsin,h]

#print axioms gaussian_microscopic_scalar_floor
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
