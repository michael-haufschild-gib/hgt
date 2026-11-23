import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.Cutoff
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ClockGrowth

/-! # A physical phase-filling deadline at inverse-exponential resolution -/
open Filter MeasureTheory Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
noncomputable section

/-- A polynomial number of angular accuracy bits in Hilbert dimension is
available on every translated interval of doubly exponential length. -/
theorem gaussian_bit_phase_filling (b : ℕ → ℕ) (hb : PolynomialInDimension b) :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∃ e : (Fin N → Bool) ≃ Fin (D-1+1), ∀ a : ℝ, ∀ v : Fin (D-1) → ℝ,
        ∃ t ∈ Icc a (a+(2:ℝ)^(D^C)), ∀ j,
          turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-v j) < 1/(2:ℝ)^(b k) := by
  let D (k : ℕ) := 2^(k+3)
  let ρ (k : ℕ) := 1/(2:ℝ)^(b k)
  let e (k : ℕ) := prefixPhaseEnergyEquiv k
  let S (k : ℕ) := phaseClockModes (e k) (ρ k)
  let F (k : ℕ) := nonconstantPacketIndexSet (phaseCubeFourierCutoff (D k-1) (ρ k)) (D k-1)
  have hp k : 0 < ρ k := by dsimp [ρ]; positivity
  have hπ k : ρ k ≤ π := (div_le_self zero_le_one (one_le_pow₀ (by norm_num))).trans (by linarith only [pi_gt_three])
  have hρ : LogPolynomialInDimension (fun k => (ρ k)⁻¹) := by
    simpa only [ρ,one_div,inv_inv] using LogPolynomialInDimension.twoPow hb
  obtain ⟨hF,hS⟩ := growing_packet_size ρ hp hρ
  have hG := ((LogPolynomialInDimension.const 8).mul (hF.add (LogPolynomialInDimension.const 1))).mul
    (inverse_margin_log_polynomial (fun k => (S k).card) hS)
  obtain ⟨C,hC⟩ := hG.bound
  refine ⟨C,?_⟩
  filter_upwards [gaussian_path_eventually_finite_mode_margin S,gaussian_path_all_prefixes_maximally_projective]
    with ω hω hspec
  filter_upwards [hω] with k hk
  intro N D' E
  let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let E' := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ
  obtain ⟨p,he⟩ := physical_sorted_order k ω (hspec k).injective
  refine ⟨p.trans (e k),?_⟩
  have hs : E ∘ (p.trans (e k)).symm = E' ∘ (e k).symm := by
    funext j
    simpa only [Function.comp_apply,Equiv.symm_trans_apply,p.apply_symm_apply] using he (p.symm ((e k).symm j))
  intro a v
  rw [hs]
  obtain ⟨t,ht,ht'⟩ := phaseCube_hit_at_calibrated_cutoff (hp k) (hπ k) (prefixModeMargin_pos k (S k).card)
    (RHTower.zeroProjectiveFrequency (E' ∘ (e k).symm)) (by
      intro f hf
      obtain ⟨m,hm,h₀,hbal,heq⟩ := balanced_mode_of_retained_phase_frequency (ρ:=ρ k) (e k) E' f hf
      rw [←heq]
      exact hk m hm h₀ hbal) a v
  refine ⟨t,⟨ht.1,ht.2.trans (add_le_add_right ?_ _)⟩,ht'⟩
  simpa only [div_eq_mul_inv,Nat.cast_one,Nat.cast_ofNat] using hC k

#print axioms gaussian_bit_phase_filling
end
end GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
