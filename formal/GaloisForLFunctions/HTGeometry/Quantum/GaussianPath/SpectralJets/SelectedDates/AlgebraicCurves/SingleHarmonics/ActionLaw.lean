import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.RatioDirections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LineActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.PhysicalPhases
import GaloisForLFunctions.HTGeometry.LocalAnalyticNullPreimage

/-! # Absolutely continuous off-pair actions on a first-return branch -/

open Set MeasureTheory Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
noncomputable section

/-- The normalized action of every balanced packet that uses a level
outside the closing pair pulls real null sets back to null sets. -/
theorem normalized_action_null {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ l, (P l).IsHermitian) (hs : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    (i j : Fin D) (hij : i≠j) (w : Fin D → ℝ) (hb : ∑ l, w l=0)
    (hout : ∃ l, l≠i ∧ l≠j ∧ w l≠0) (S : Set ℝ) (hS : volume S=0) :
    volume (simpleEnsembleLocus hP ∩ (fun x => normalizedAction w (sortedEnsembleSpectrum hP x) i j) ⁻¹' S)=0 := by
  let E := sortedEnsembleSpectrum hP
  apply analytic_preimage_volume_eq_zero_isOpen (isOpen_simpleEnsembleLocus hP) _ _ S hS
  · intro x hx
    have h := analyticAt_sortedEnsembleSpectrum hP hx
    exact (Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul (h l)).div
      ((h i).sub (h j)) (sub_ne_zero.mpr ((injective_sortedEnsembleSpectrum hP hx).ne hij))
  · intro V hV hne hsub
    obtain ⟨x,hx⟩ := hne
    obtain ⟨y,hy,hh⟩ := exists_distinct_ratios hP hs hij (fun _ : Unit => w) (fun _ => hb) (fun _ => hout)
      (fun _ => normalizedAction w (E x) i j) hV ⟨x,hx,hsub hx⟩
    exact ⟨y,hy.1,x,hx,hh ()⟩

/-- This remains true under any absolutely continuous restriction of the
Gaussian couplings, so selection of the particular entry branch is allowed. -/
theorem physical_normalized_action_null (k : ℕ) (i j : Fin (2^(k+3))) (hij : i≠j)
    (w : Fin (2^(k+3)) → ℝ) (hb : ∑ l, w l=0) (hout : ∃ l, l≠i ∧ l≠j ∧ w l≠0)
    (S : Set ℝ) (hS : volume S=0) :
    ∀ᵐ x ∂(volume : Measure (Fin (Fintype.card (ChainLabel (k+3))) → ℝ)),
      normalizedAction w (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x) i j∉S := by
  let hP := chainPauliFin_isHermitian (k+3)
  have hsimple : ∀ᵐ x ∂volume, MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP x).eigenvalues :=
    ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
  have h := normalized_action_null hP (chainPauliFin_spectrumEscapesRealRelations k) i j hij w hb hout S hS
  filter_upwards [hsimple,measure_eq_zero_iff_ae_notMem.mp h] with x hx hh
  exact fun hbad => hh ⟨hx.injective,hbad⟩

#print axioms physical_normalized_action_null
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
