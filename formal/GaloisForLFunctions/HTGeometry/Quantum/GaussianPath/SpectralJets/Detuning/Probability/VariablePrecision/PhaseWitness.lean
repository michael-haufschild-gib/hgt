import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.FiniteMargin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # Phase covering on each prefix with a positive finite-mode margin -/
open Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Retained Fourier modes used to hit a phase cube of angular radius ρ. -/
abbrev precisionModes (k : ℕ) (ρ : ℝ) := phaseClockModes (prefixPhaseEnergyEquiv k) ρ

/-- Numerator of the Fourier covering deadline at angular radius ρ. -/
def precisionPrice (k : ℕ) (ρ : ℝ) : ℝ :=
  let d := 2^(k+3)-1
  8*(((nonconstantPacketIndexSet (phaseCubeFourierCutoff d ρ) d).card:ℝ)+1)

/-- A finite-mode margin dates every phase cube from every origin on this draw. -/
theorem precision_cover_of_margin (k : ℕ) (ω : PathPauliDisorder) {ρ δ : ℝ}
    (hρ : 0<ρ) (hπ : ρ≤π) (hδ : 0<δ)
    (hi : Function.Injective (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues)
    (hx : (fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)) ∉
      smallBalancedMode (k+3) (precisionModes k ρ) δ) :
    let N := k+3
    let D : ℕ := 2^N
    let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
    ∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ u : ℝ, ∀ z : Fin (D-1) → ℝ,
      ∃ t ∈ Icc u (u+precisionPrice k ρ/δ), ∀ j,
        turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-z j)<ρ := by
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
  refine phaseCube_hit_at_calibrated_cutoff hρ hπ hδ (RHTower.zeroProjectiveFrequency (f ∘ e.symm)) ?_ u z
  intro v hv
  obtain ⟨m,hm,hn,hbal,heq⟩ := balanced_mode_of_retained_phase_frequency (ρ:=ρ) e f v hv
  rw [←heq]
  exact le_of_not_gt fun hs => hx ⟨m,hm,hn,hbal,hs⟩

#print axioms precision_cover_of_margin
end
end GaloisForLFunctions.HTGeometry.SpectralJets
