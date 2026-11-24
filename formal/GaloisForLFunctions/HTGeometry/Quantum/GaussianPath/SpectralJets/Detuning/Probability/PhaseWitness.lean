import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.FiniteMargin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # Phase covering on each prefix with a positive finite-mode margin -/
open Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Retained Fourier modes used to hit a phase cube of angular radius 1/80. -/
abbrev retainedClockModes (k : ℕ) := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)

/-- Numerator of the Fourier covering deadline at physical angular radius 1/80. -/
def phaseClockPrice (k : ℕ) : ℝ :=
  let d := 2^(k+3)-1
  8*(((nonconstantPacketIndexSet (phaseCubeFourierCutoff d (1/80)) d).card:ℝ)+1)

/-- A finite-mode margin dates every phase cube from every origin on this draw. -/
theorem phase_cover_of_margin (k : ℕ) (ω : PathPauliDisorder) {δ : ℝ} (hδ : 0<δ)
    (hi : Function.Injective (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues)
    (hx : (fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)) ∉
      smallBalancedMode (k+3) (retainedClockModes k) δ) :
    let N := k+3
    let D : ℕ := 2^N
    let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
    ∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ u : ℝ, ∀ z : Fin (D-1) → ℝ,
      ∃ t ∈ Icc u (u+phaseClockPrice k/δ), ∀ j,
        turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-z j)<1/80 := by
  intro N D E
  let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let f := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x
  let e := prefixPhaseEnergyEquiv k
  obtain ⟨p,hp⟩ := physical_sorted_order k ω hi
  refine ⟨p.trans e,?_⟩
  have he : E ∘ (p.trans e).symm = f ∘ e.symm := by
    funext j
    simpa only [Function.comp_apply,Equiv.symm_trans_apply,p.apply_symm_apply] using hp (p.symm (e.symm j))
  rw [he]
  intro u z
  refine phaseCube_hit_at_calibrated_cutoff (by norm_num : (0:ℝ)<1/80)
    (by linarith only [pi_gt_three]) hδ (RHTower.zeroProjectiveFrequency (f ∘ e.symm)) ?_ u z
  intro v hv
  obtain ⟨m,hm,hn,hbal,heq⟩ := balanced_mode_of_retained_phase_frequency (ρ:=1/80) e f v hv
  rw [←heq]
  exact le_of_not_gt fun hs => hx ⟨m,hm,hn,hbal,hs⟩

#print axioms phase_cover_of_margin
end
end GaloisForLFunctions.HTGeometry.SpectralJets
