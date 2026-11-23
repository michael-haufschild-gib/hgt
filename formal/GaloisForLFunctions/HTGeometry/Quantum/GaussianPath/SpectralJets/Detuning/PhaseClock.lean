import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PrefixModes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.HorizonGrowth

/-! # A phase-filling clock from finite spectral derivative bounds -/

open Matrix MeasureTheory Filter Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Absolute horizon at angular tolerance 1/80. -/
def derivativePhaseHorizon (k : ℕ) : ℝ :=
  let d := 2^(k+3)-1
  let S := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)
  8*(((nonconstantPacketIndexSet (phaseCubeFourierCutoff d (1/80)) d).card:ℝ)+1)/prefixModeMargin k S.card

/-- Each retained Fourier frequency is a nonzero balanced integer sum of the energies. -/
theorem balanced_mode_of_retained_phase_frequency {D d : ℕ} {ρ : ℝ} (e : Fin D ≃ Fin (d+1)) (E : Fin D → ℝ)
    (p : Fin d → ℕ × ℕ) (hp : p ∈ nonconstantPacketIndexSet (phaseCubeFourierCutoff d ρ) d) :
    ∃ m ∈ phaseClockModes e ρ, m ≠ 0 ∧ ∑ i, m i = 0 ∧
      ∑ i, (m i:ℝ)*E i = packetFreq (RHTower.zeroProjectiveFrequency (E ∘ e.symm)) p := by
  refine ⟨liftedPhaseMode e p,Finset.mem_image_of_mem _ hp,?_,?_,?_⟩
  · intro hz
    apply packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet hp
    funext j
    have h := congrFun hz (e.symm j.succ)
    simpa only [liftedPhaseMode,e.apply_symm_apply,Fin.cases_succ,Pi.zero_apply,neg_eq_zero] using h
  · unfold liftedPhaseMode
    rw [Equiv.sum_comp e,Fin.sum_univ_succ]
    simp
  · rw [← Equiv.sum_comp e.symm (fun i => (liftedPhaseMode e p i:ℝ)*E i),Fin.sum_univ_succ]
    simp only [liftedPhaseMode,e.apply_symm_apply,Fin.cases_zero,Fin.cases_succ,Int.cast_sum,Int.cast_neg,
      packetFreq,RHTower.zeroProjectiveFrequency,Function.comp_apply,packetCharacter,Int.cast_sub,Int.cast_natCast]
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- In the sorted energy labeling, every relative-phase cube is visited
within the explicit horizon, from every time origin. -/
theorem gaussian_path_sorted_derivative_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ
      ∀ u : ℝ, ∀ c : Fin (2^N-1) → ℝ, ∃ t ∈ Icc u (u+derivativePhaseHorizon k), ∀ j,
        turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ (prefixPhaseEnergyEquiv k).symm) j-c j) < 1/80 := by
  let S (k : ℕ) := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)
  filter_upwards [gaussian_path_eventually_finite_mode_margin S] with ω hω
  filter_upwards [hω] with k hk
  intro N θ E u c
  refine phaseCube_hit_at_calibrated_cutoff (by norm_num : (0:ℝ) < 1/80) (by linarith only [pi_gt_three])
    (prefixModeMargin_pos k (S k).card) (RHTower.zeroProjectiveFrequency (E ∘ (prefixPhaseEnergyEquiv k).symm)) ?_ u c
  intro p hp
  obtain ⟨m,hm,hn,hb,he⟩ := balanced_mode_of_retained_phase_frequency (ρ:=1/80) (prefixPhaseEnergyEquiv k) E p hp
  rw [← he]
  exact hk m hm hn hb

/-- Simple physical energies agree with the sorted ensemble energies up to a permutation. -/
theorem physical_sorted_order (k : ℕ) (ω : PathPauliDisorder)
    (hi : Function.Injective (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues) :
    let N := k+3
    let u := pathPauliDisorderShell ω (k+1)
    let θ := fun i => u (pathCoeffEquiv (k+1) i)
    ∃ e : (Fin N → Bool) ≃ Fin (2^N), ∀ j,
      (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j = sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ (e j) := by
  classical
  intro N u θ
  let e₀ := qubitConfigFin N
  let H := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let G := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian N) θ
  let E := G.eigenvalues
  have hg := range_eigenvalues_reindex e₀ H
  have he := isHermitian_eigenvalues_congr (isHermitian_reindex e₀ H) G (reindex_pathHamiltonian u)
  rw [he] at hg
  have hmem (i : Fin (2^N)) : ∃ j, H.eigenvalues (e₀.symm i) = sortedTuple E j := by
    have h : H.eigenvalues (e₀.symm i) ∈ Set.range E := by rw [show Set.range E = Set.range H.eigenvalues from hg]; exact Set.mem_range_self _
    obtain ⟨a,ha⟩ := h
    obtain ⟨j,hj⟩ := exists_sortedTuple_eq E a
    exact ⟨j,ha.symm.trans hj⟩
  choose s hs using hmem
  have hs' : Function.Injective s := fun i j hij =>
    e₀.symm.injective (hi ((hs i).trans ((congrArg (sortedTuple E) hij).trans (hs j).symm)))
  let p := Equiv.ofBijective s hs'.bijective_of_finite
  refine ⟨e₀.trans p,fun j => ?_⟩
  change H.eigenvalues j = sortedTuple E (s (e₀ j))
  simpa only [e₀.symm_apply_apply] using hs (e₀ j)

/-- The same cube clock for the actual spectral phases of one infinite
Gaussian Pauli chain, in an ordering chosen once for each prefix. -/
theorem gaussian_path_derivative_phase_filling :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∃ e : (Fin N → Bool) ≃ Fin ((2^N-1)+1), ∀ u : ℝ, ∀ c : Fin (2^N-1) → ℝ,
        ∃ t ∈ Icc u (u+derivativePhaseHorizon k), ∀ j,
          turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-c j) < 1/80 := by
  filter_upwards [gaussian_path_sorted_derivative_clock,gaussian_path_all_prefixes_maximally_projective] with ω hω hspec
  filter_upwards [hω] with k hk
  intro N E
  obtain ⟨p,hp⟩ := physical_sorted_order k ω (hspec k).injective
  let e := prefixPhaseEnergyEquiv k
  refine ⟨p.trans e,?_⟩
  let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have he : E ∘ (p.trans e).symm = sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ ∘ e.symm := by
    funext j
    simpa only [Function.comp_apply,Equiv.symm_trans_apply,p.apply_symm_apply] using hp (p.symm (e.symm j))
  rw [he]
  exact hk

#print axioms gaussian_path_derivative_phase_filling
end
end GaloisForLFunctions.HTGeometry.SpectralJets
