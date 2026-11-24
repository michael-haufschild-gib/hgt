import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.SpectralForms
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # All balanced integer action clocks on one frozen Gaussian chain -/

open Set MeasureTheory Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section

private theorem sorted_law (k n : ℕ) (A : Fin (n+1)→Fin (2^(k+3))→ℤ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) θ
      (∀ i, SpectralCharacterBalanced (A i)) → IndependentRows A → action (A 0) E≠0 →
        ¬KleinbockMargulis.VWMA (ratios A E) := by
  by_cases h : (∀ i, SpectralCharacterBalanced (A i)) ∧ IndependentRows A
  · let hP := chainPauliFin_isHermitian (k+3)
    have hnull := spectral_form_null hP (chainPauliFin_spectrumEscapesRealRelations k) A h.1 h.2
    have hv : ∀ᵐ x ∂volume, ¬(x∈simpleEnsembleLocus hP ∧ action (A 0) (sortedEnsembleSpectrum hP x)≠0 ∧
        KleinbockMargulis.VWMA (ratios A (sortedEnsembleSpectrum hP x))) :=
      ae_iff.mpr (by simpa only [not_not] using hnull)
    have hs : ∀ᵐ x ∂volume, MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP x).eigenvalues :=
      ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
    let d := Fintype.card (ChainLabel (k+3))
    have hac : centredProductGaussian (Fin d) 1 ≪ volume := by
      simpa [centredProductGaussian] using productGaussian_absolutelyContinuous d one_ne_zero (fun _ => 0)
    have hh := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae (hac.ae_le (hs.and hv))
    filter_upwards [hh] with ω hω
    intro θ E _ _ hd hw
    exact hω.2 ⟨hω.1.injective,hd,hw⟩
  · filter_upwards with ω
    intro θ E hb hi
    exact (h ⟨hb,hi⟩).elim

/-- Every collection of independent balanced integer energy forms gives
a nonzero physical clock and multiplicatively extremal clock ratios.
The rows and the prefix may be selected after the disorder is known. -/
theorem gaussian_spectral_forms :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k n : ℕ,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ A : Fin (n+1)→(Fin (k+3)→Bool)→ℤ, (∀ i, SpectralCharacterBalanced (A i)) → IndependentRows A →
        action (A 0) E≠0 ∧ ¬KleinbockMargulis.VWMA (ratios A E) := by
  have h (k n : ℕ) := ae_all_iff.mpr (sorted_law k n)
  filter_upwards [ae_all_iff.mpr (fun k => ae_all_iff.mpr (h k)),gaussian_path_all_prefixes_maximally_projective]
    with ω hall hspec k n
  intro E A hb hi
  have hd : action (A 0) E≠0 := by
    intro hz
    have hrow := hspec k (A 0) (hb 0) hz
    let c := Fin.cons (α:=fun _ => ℝ) 1 (0 : Fin n→ℝ)
    have hc := hi c (fun j => by
      rw [Fin.sum_univ_succ]
      simp only [c,Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,zero_mul,sum_const_zero,add_zero,one_mul,hrow,Int.cast_zero])
    exact one_ne_zero (congrFun hc 0)
  refine ⟨hd,?_⟩
  obtain ⟨e,he⟩ := SpectralJets.physical_sorted_order k ω (hspec k).injective
  let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let F := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) θ
  let B := fun i j => A i (e.symm j)
  have hb' (i) : SpectralCharacterBalanced (B i) := (Equiv.sum_comp e.symm (A i)).trans (hb i)
  have hi' : IndependentRows B := by
    intro c hc
    apply hi c
    intro j
    simpa only [B,e.symm_apply_apply] using hc (e j)
  have ha (i) : action (A i) E=action (B i) F := by
    rw [action,action,←Equiv.sum_comp e (fun j => (B i j:ℝ)*F j)]
    exact sum_congr rfl fun j _ => by simp only [B,e.symm_apply_apply]; rw [show E j=F (e j) from he j]
  have hh := hall k n B hb' hi' (ha 0 ▸ hd)
  have heq : ratios A E=ratios B F := funext fun i => (congrArg₂ (fun x y : ℝ => x/y) (ha i.succ) (ha 0))
  rw [heq]
  exact hh

#print axioms gaussian_spectral_forms
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
