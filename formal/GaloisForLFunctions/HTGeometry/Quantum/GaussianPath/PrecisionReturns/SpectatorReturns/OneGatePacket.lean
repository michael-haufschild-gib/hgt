import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PhaseCenters
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.TwoWirePhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.FirstVisit

/-! # A one-gate fit to four equal-multiplicity spectral packets -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

/-- In the energy basis the error of a diagonal comparison is the
maximum of its coordinate errors. -/
theorem diagonal_fit_in_energy_basis {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ)
    (p : (Fin N→Bool) → ℂ) {ε : ℝ} (h : ∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-p i‖≤ε) :
    let V := star H.2.isHermitian.eigenvectorUnitary
    ‖V.val*unitaryEvolution H.val t*star V.val-diagonal p‖≤ε := by
  let V := H.2.isHermitian.eigenvectorUnitary
  let D := diagonal (fun i => anchorPhase H.2.isHermitian.eigenvalues i t)
  have hu : unitaryEvolution H.val t=V.val*D*star V.val := unitaryEvolution_spectral H.2.isHermitian t
  have hd : star V.val*unitaryEvolution H.val t*V.val=D := calc
    _ = (star V.val*V.val)*D*(star V.val*V.val) := by rw [hu]; simp only [mul_assoc]
    _ = _ := by rw [V.property.1,one_mul,mul_one]
  change ‖star V.val*unitaryEvolution H.val t*star (star V.val)-diagonal p‖≤ε
  rw [star_star,hd,Matrix.diagonal_sub,l2_opNorm_diagonal,pi_norm_le_iff_of_nonempty]
  exact h

/-- Four unit phases indexed by two basis bits are synthesized by one
gate. Conjugation to the energy basis preserves its fitting tolerance. -/
theorem one_gate_of_four_packets {N : ℕ} (H : selfAdjoint (Register N)) (a b : Fin N) (hab : a≠b)
    (f : Bool×Bool → ℂ) (hf : ∀ j, ‖f j‖=1) {t ε : ℝ}
    (hne : ∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-f (i a,i b)‖≤ε) :
    t ∈ SpectralApproximation.affordableDates H 1 ε := by
  obtain ⟨z,hz,C,hC,hdiag⟩ := SpectralSorting.realizes_pair_phase a b hab f hf
  refine ⟨star H.2.isHermitian.eigenvectorUnitary,z,hz,C,hC,?_⟩
  rw [←hdiag]
  exact diagonal_fit_in_energy_basis H t _ hne

/-- Every two-bit label occurs among the energy coordinates. -/
theorem two_bits_surjective {N : ℕ} (a b : Fin N) (hab : a≠b) :
    Function.Surjective (fun i : Fin N→Bool => (i a,i b)) := by
  let e := splitTwoQubitConfig a b hab
  intro x
  exact ⟨e.symm (x,fun _ => false),congrArg Prod.fst (e.apply_symm_apply (x,fun _ => false))⟩

#print axioms one_gate_of_four_packets
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
