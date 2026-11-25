import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.PhaseDistribution
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # All relative phases on a shift of the selected first-wait clock -/

open Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
open PrescribedTimes
noncomputable section

private abbrev point (k : ℕ) (ω : PathPauliDisorder) : PrefixIndex (k+1) → ℝ :=
  fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)

/-- On a single full-measure event, every prefix and every crossing
and return budget have the shifted-clock law. The shift and integer
schedule may be prescribed separately for each prefix. -/
theorem gaussian_shifted_phase_law (b : ℕ → ℕ → ℤ) (hb : ∀ k, Function.Injective (b k))
    (h : ℕ → ℝ) (hh : ∀ k, h k ≠ 0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∃ e : (Fin N → Bool) ≃ Fin ((2^N-1)+1), ∀ j s : ℕ,
        let τ := crossingWait (k+1) j s (point k ω)+h k
        0<τ → ∀ a : ℝ, Tendsto (integerClockPrefixLaw (fun i =>
          finiteClockPhasePoint (RHTower.zeroProjectiveFrequency (E ∘ e.symm)) (a+(b k i:ℝ)*τ))) atTop
          (𝓝 (finiteTorusHaarProbabilityMeasure (Fin (2^N-1)))) := by
  apply ae_all_iff.mpr
  intro k
  let N := k+3
  let p := prefixPhaseEnergyEquiv k
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian N)
  let w (x : PrefixIndex (k+1) → ℝ) := RHTower.zeroProjectiveFrequency (E x ∘ p.symm)
  have hE := (continuous_sortedEnsembleSpectrum (chainPauliFin_isHermitian N)).measurable
  have hw : Measurable w := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply (p.symm 0)).comp hE).sub ((measurable_pi_apply (p.symm i.succ)).comp hE)
  have hs (r : ℝ) (hr : 0<r) (x : PrefixIndex (k+1) → ℝ) (i) : w (r • x) i=r*w x i := by
    change E (fun l => r*x l) (p.symm 0) - E (fun l => r*x l) (p.symm i.succ)=_
    simp only [E,sortedEnsembleSpectrum_const_mul _ hr,w,RHTower.zeroProjectiveFrequency,
      Function.comp_apply,mul_sub]
  have hg : centredProductGaussian (PrefixIndex (k+1)) 1 ≪ volume :=
    productGaussian_absolutelyContinuous _ one_ne_zero _
  have hfreq (j s : ℕ) := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae
    (hg.ae_le (shifted_phase_law (b k) (hb k) w hw hs (crossingWait (k+1) j s)
      (measurable_crossingWait _ _ _) (fun _ hr => smul_crossingWait _ _ _ hr) (hh k)))
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hfreq j)),
    gaussian_path_all_prefixes_maximally_projective] with ω hω hmax
  intro _ energies
  obtain ⟨q,hq⟩ := SpectralJets.physical_sorted_order k ω (hmax k).injective
  let e := q.trans p
  have he : energies ∘ e.symm = E (point k ω) ∘ p.symm := by
    funext i
    simpa only [e,Function.comp_apply,Equiv.symm_trans_apply,q.apply_symm_apply] using hq (q.symm (p.symm i))
  refine ⟨e,?_⟩
  rw [he]
  have hind : RationallyIndependentFrequency (w (point k ω)) := by
    apply RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent
    rw [←he]
    exact (hmax k).comp_equiv e.symm
  exact fun j s hp => hω j s hp hind

#print axioms gaussian_shifted_phase_law
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
