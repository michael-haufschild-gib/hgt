import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.ModeHeights

/-! # One phase-filling clock at every resolution of a frozen prefix -/
open Filter MeasureTheory Set Real Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
open private lifted_mass_le from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.HorizonGrowth
noncomputable section

/-- Every Fourier frequency retained at tolerance ρ has height at most
2dM, where d is the relative phase dimension and M the Fourier cutoff. -/
def phaseHorizon (k : ℕ) (ρ : ℝ) : ℝ :=
  let d := 2^(k+3)-1
  let M := phaseCubeFourierCutoff d ρ
  8*(((nonconstantPacketIndexSet M d).card:ℝ)+1)/heightMargin k (2*d*M)

private theorem packet_height {D d : ℕ} (e : Fin D ≃ Fin (d+1)) {ρ : ℝ}
    {m : Fin D → ℤ} (hm : m∈phaseClockModes e ρ) (i : Fin D) :
    (m i).natAbs ≤ 2*d*phaseCubeFourierCutoff d ρ := by
  classical
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
  have h := (Finset.single_le_sum (s:=Finset.univ) (f:=fun j => |(liftedPhaseMode e p j:ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans (lifted_mass_le e p hp)
  rw [←Nat.cast_le (α:=ℤ),Int.natCast_natAbs]
  exact_mod_cast h

/-- The tolerance may be chosen after reading the physical spectrum. Every
target and origin shares the same explicit deadline at that tolerance. -/
theorem gaussian_all_precision_phase_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let d := 2^N-1
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      ∀ ρ ∈ Ioc (0:ℝ) π, ∀ u : ℝ, ∀ c : Fin d → ℝ,
        ∃ t ∈ Icc u (u+phaseHorizon k ρ), ∀ j,
          turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-c j) < ρ := by
  filter_upwards [gaussian_all_heights] with ω hw
  filter_upwards [hw] with k hk
  intro N d E e ρ hρ u c
  let a := qubitConfigFin N
  let b := prefixPhaseEnergyEquiv k
  let F := E ∘ a.symm
  let H := 2*d*phaseCubeFourierCutoff d ρ
  change ∃ t ∈ Icc u (u+phaseHorizon k ρ), ∀ j,
    turnDist (t*RHTower.zeroProjectiveFrequency (F ∘ b.symm) j-c j) < ρ
  apply phaseCube_hit_at_calibrated_cutoff hρ.1 hρ.2 (heightMargin_pos k H)
  intro p hp
  obtain ⟨m,hm,hne,hbal,he⟩ := balanced_mode_of_retained_phase_frequency (ρ:=ρ) b F p hp
  have hn : m ∘ a ≠ 0 := by
    intro hz
    apply hne
    funext j
    simpa only [Function.comp_apply,a.apply_symm_apply,Pi.zero_apply] using congrFun hz (a.symm j)
  have h := hk H (m ∘ a) hn ((Equiv.sum_comp a m).trans hbal) (fun i => packet_height b hm (a i))
  rw [←he,←Equiv.sum_comp a (fun i => (m i:ℝ)*F i)]
  simpa only [F,Function.comp_apply,a.symm_apply_apply] using h

#print axioms gaussian_all_precision_phase_clock
end
end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
