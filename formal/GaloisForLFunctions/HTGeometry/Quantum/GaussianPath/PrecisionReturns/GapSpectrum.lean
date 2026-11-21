import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import GaloisForLFunctions.HTGeometry.PathShellProjectiveGenericity
import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalExtremality
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.RHTower.FullProjectiveChoiPhysicalSpectrumLaw

/-! # Extremal gap ratios of the actual Gaussian path generator -/
open Matrix MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section

private theorem sorted_reindex {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}
    (q : I ≃ Fin D) {H : Matrix I I ℂ} (h : H.IsHermitian) :
    sortedTuple (h.reindex q).eigenvalues = sortedTuple (h.eigenvalues ∘ q.symm) := by
  obtain rfl : D = Fintype.card I := ((Fintype.card_congr q).trans (Fintype.card_fin D)).symm
  exact sortedTuple_eigenvalues_reindex q h

private theorem labels (k : ℕ) (u : PathShell (k+1)) :
    let N := k+3
    let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
    let x := fun i => u (pathCoeffEquiv (k+1) i)
    ∃ e : (Fin N → Bool) ≃ Fin (2^N), E ∘ e.symm = sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x := by
  classical
  intro N E x
  let q := qubitConfigFin N
  let raw := E ∘ q.symm
  let h := (isSelfAdjoint_pathHamiltonian u).isHermitian
  have he := isHermitian_eigenvalues_congr (h.reindex q) (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian N) x) (reindex_pathHamiltonian u)
  have hs := (sorted_reindex q h).symm.trans (congrArg sortedTuple he)
  exact ⟨q.trans (Tuple.sort raw).symm,hs⟩

/-- On one disorder event, every prefix has a spectral labeling with a
positive clock gap and an extremal vector of all other gap ratios. -/
theorem gaussian_gap_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let d := 2^N-3
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∃ e : (Fin N → Bool) ≃ Fin (d+3), 0 < E (e.symm 1)-E (e.symm 0) ∧
        ¬KleinbockMargulis.VWA (anchoredGapRatioMap (E ∘ e.symm) 0 1 (fun i => i.succ.succ)) := by
  apply ae_all_iff.mpr
  intro k
  let N := k+3
  let d := 2^N-3
  have hdim : 3 ≤ (2:ℕ)^N := (by decide : 3 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega))
  let f : Fin (d+3) ≃ Fin (2^N) := finCongr (by dsimp [d]; omega)
  let L (i : Fin (d+1)) := f i.succ.succ
  let hP := chainPauliFin_isHermitian N
  have hinj : Function.Injective L := f.injective.comp ((Fin.succ_injective _).comp (Fin.succ_injective _))
  have hd (i : Fin (d+1)) : i.succ.succ ≠ (0 : Fin (d+3)) := Fin.succ_ne_zero _
  have hd' (i : Fin (d+1)) : i.succ.succ ≠ (1 : Fin (d+3)) := by
    intro h
    have he := congrArg Fin.val h
    change i.val+1+1=1 at he
    omega
  have h01 : (0 : Fin (d+3)) < 1 := by exact Fin.mk_lt_mk.mpr (by simp)
  have hz := volume_vwa_sortedGapRatio_eq_zero (by omega : 0<d+1) hP (chainPauliFin_spectrumEscapesRealRelations k)
    hinj (fun i h => hd i (f.injective h)) (fun i h => hd' i (f.injective h)) (fun h => h01.ne (f.injective h))
  have hg : ∀ᵐ x ∂volume, x ∈ simpleEnsembleLocus hP ∧
      ¬KleinbockMargulis.VWA (anchoredGapRatioMap (sortedEnsembleSpectrum hP x) (f 0) (f 1) L) := by
    have hs : ∀ᵐ x ∂volume, MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP x).eigenvalues :=
      ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
    have hv : ∀ᵐ x ∂volume, ¬(x ∈ simpleEnsembleLocus hP ∧ KleinbockMargulis.VWA
        (anchoredGapRatioMap (sortedEnsembleSpectrum hP x) (f 0) (f 1) L)) := ae_iff.mpr (by simpa only [not_not] using hz)
    filter_upwards [hs,hv] with x hx hh
    exact ⟨hx.injective,fun hvwa => hh ⟨hx.injective,hvwa⟩⟩
  let p := Fintype.card (ChainLabel N)
  have hac : centredProductGaussian (Fin p) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous p one_ne_zero (fun _ => 0)
  have ha := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae (hac.ae_le hg)
  filter_upwards [ha] with ω hω
  obtain ⟨q,hq⟩ := labels k (pathPauliDisorderShell ω (k+1))
  let e := q.trans f.symm
  refine ⟨e,?_,?_⟩
  · have h := RHTower.sortedEnsembleSpectrum_clockGap_pos hP hω.1 (show f 0 < f 1 from h01)
    rw [←hq] at h
    exact h
  · have h := hω.2
    rw [←hq] at h
    exact h

#print axioms gaussian_gap_clock
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
