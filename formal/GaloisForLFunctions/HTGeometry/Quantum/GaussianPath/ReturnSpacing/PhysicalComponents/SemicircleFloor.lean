import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.AngularProfile

/-! # Physical scalar exclusion beyond the first spectral semicircle -/
open Matrix Real Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- In the first turn the two extreme energies detect the middle range.
Past nine tenths of a turn, opposite configurations detect a fixed angle. -/
theorem gaussian_scalar_semicircle_margin (B : ℝ) (hB : 0<B) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
      ∀ t : ℝ, 0<t → t≤B/N → π ≤ t*circuitHamiltonianSpectralWidth H →
        201/1000 < orbitCircuitDistance H 0 t := by
  have slope (x : ℝ) (hx : 0≤x) (hsmall : x≤π/6) : 3*x/π ≤ sin x := by
    have h := QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le (A:=π/6) (x:=x)
      (by positivity) (by linarith only [pi_pos]) hx hsmall
    rw [sin_pi_div_six] at h
    exact (show 3*x/π=(1/2/(π/6))*x by field_simp [pi_ne_zero]; ring).le.trans h
  filter_upwards [gaussian_chord_from_width B hB] with ω hh
  filter_upwards [hh] with n hn
  intro N u H t ht hshort hlate
  let a := t*circuitHamiltonianSpectralWidth H/2
  by_cases h : 9*π/5 ≤ t*circuitHamiltonianSpectralWidth H
  · have hp := hn t ht hshort (18*π/125) (by positivity) (by linarith only [pi_pos]) (by linarith only [h])
    rw [show 18*π/125/2=9*π/125 by ring] at hp
    have hs := slope (9*π/125) (by positivity) (by linarith only [pi_pos])
    rw [show 3*(9*π/125)/π=27/125 by field_simp [pi_ne_zero]; ring] at hs
    linarith only [hp,hs]
  · have hm := abs_sin_spectralWidth_le_zeroGateDistance H t
    rw [←mul_div_assoc] at hm
    change |sin a| ≤ _ at hm
    have ha : π/10 ≤ π-a := by dsimp only [a]; linarith only [h]
    have hb : π-a ≤ π/2 := by dsimp only [a]; linarith only [hlate]
    have hs := slope (π/10) (by positivity) (by linarith only [pi_pos])
    rw [show 3*(π/10)/π=3/10 by field_simp [pi_ne_zero]] at hs
    have hs' := sin_le_sin_of_le_of_le_pi_div_two (show -(π/2) ≤ π/10 by linarith only [pi_pos]) hb ha
    rw [sin_pi_sub] at hs'
    linarith only [hs,hs',le_abs_self (sin a),hm]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
