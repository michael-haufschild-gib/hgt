import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.RealRelations
import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality

/-! # Local variation of finitely many energy ratios -/

open Set Matrix MeasureTheory Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- Near a simple spectrum one can change every specified balanced action
relative to the closing gap at once, provided each action uses a level
outside the closing pair. The avoided values may be prescribed separately. -/
theorem exists_distinct_ratios {m D : ℕ} {P : Fin m → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (hs : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    {i j : Fin D} (hij : i≠j) {L : Type*} [Fintype L]
    (w : L → Fin D → ℝ) (hb : ∀ l, ∑ k, w l k=0)
    (hout : ∀ l, ∃ k, k≠i ∧ k≠j ∧ w l k≠0) (z : L → ℝ)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hne : (U ∩ simpleEnsembleLocus hP).Nonempty) :
    ∃ y ∈ U ∩ simpleEnsembleLocus hP, ∀ l,
      (∑ k, w l k*sortedEnsembleSpectrum hP y k) /
        (sortedEnsembleSpectrum hP y i-sortedEnsembleSpectrum hP y j) ≠ z l := by
  classical
  let d (k : Fin D) : ℝ := (if k=i then 1 else 0)-(if k=j then 1 else 0)
  have hd : ∑ k, d k=0 := by simp [d,sum_sub_distrib]
  have ha (E : Fin D → ℝ) : ∑ k, d k*E k=E i-E j := by
    simp [d,sub_mul,ite_mul,sum_sub_distrib]
  let c (l : L) (k : Fin D) := w l k-z l*d k
  have hbal (l : L) : ∑ k, c l k=0 := by simp only [c,sum_sub_distrib,←mul_sum,hd,hb,mul_zero,sub_zero]
  have hn (l : L) : c l≠0 := by
    obtain ⟨k,hki,hkj,hk⟩ := hout l
    intro h
    apply hk
    simpa only [c,d,if_neg hki,if_neg hkj,sub_self,mul_zero,sub_zero,Pi.zero_apply] using congrFun h k
  have hcon := ae_all_iff.mpr fun l => FirstGate.ae_no_fixed_real_relation P hs (c l) (hbal l) (hn l)
  obtain ⟨y,hy,hys⟩ := (Measure.dense_of_ae hcon).exists_mem_open (hU.inter (isOpen_simpleEnsembleLocus hP)) hne
  let E := sortedEnsembleSpectrum hP y
  have he : Function.Injective E := injective_sortedTuple hys.2
  refine ⟨y,hys,?_⟩
  intro l hl
  apply hy l E he (matrixCharpolyRelation_sortedEnsembleSpectrum hP y)
  have heq := (div_eq_iff (sub_ne_zero.mpr (he.ne hij))).mp hl
  simp only [c,sub_mul,mul_assoc,sum_sub_distrib,←mul_sum,ha]
  exact sub_eq_zero.mpr heq

#print axioms exists_distinct_ratios
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
