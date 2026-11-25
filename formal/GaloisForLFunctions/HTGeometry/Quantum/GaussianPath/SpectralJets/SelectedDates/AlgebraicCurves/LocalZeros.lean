import GaloisForLFunctions.HTGeometry.LocalAnalyticNullPreimage

/-! # Null zero sets of nonvanishing analytic germs on a spectral chart -/

open Set MeasureTheory Metric Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- A locally analytic complex function whose zero set contains no
open ball has a null zero set on the whole open parameter domain. -/
theorem analytic_zero_null {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f : (Fin n → ℝ) → ℂ} (hf : AnalyticOnNhd ℝ f U)
    (hn : ∀ x ∈ U, ∀ r > (0:ℝ), ball x r ⊆ U → ∃ y ∈ ball x r, f y≠0) :
    volume {x ∈ U | f x=0}=0 := by
  classical
  let Z := {x ∈ U | f x=0}
  have H (x : Z) : ∃ r > (0:ℝ), volume (ball x.val r ∩ Z)=0 := by
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU x.val x.property.1
    obtain ⟨y,hy,hne⟩ := hn x.val x.property.1 r hr hsub
    obtain ⟨L,hL⟩ : ∃ L : ℂ →L[ℝ] ℝ, L (f y)≠0 := by
      by_cases hr : (f y).re=0
      · exact ⟨Complex.imCLM,fun hi => hne (Complex.ext hr hi)⟩
      · exact ⟨Complex.reCLM,hr⟩
    have hg : AnalyticOnNhd ℝ (fun u => L (f u)) U :=
      fun u hu => (L.analyticAt _).comp (hf u hu)
    have hdiff : L (f x.val) ≠ L (f y) := by rw [x.property.2,map_zero]; exact hL.symm
    have hnull := analytic_preimage_volume_eq_zero_ball hr hsub hg
      ⟨x.val,mem_ball_self hr,y,hy,hdiff⟩ ({0}:Set ℝ) (measure_singleton _)
    have hinc : ball x.val r ∩ Z ⊆ ball x.val r ∩ (fun u => L (f u)) ⁻¹' ({0} : Set ℝ) := by
      intro u hu
      refine ⟨hu.1,?_⟩
      change L (f u)=0
      rw [hu.2.2,map_zero]
    exact ⟨r,hr,measure_mono_null hinc hnull⟩
  choose r hr hz using H
  let B (x : Z) := ball x.val (r x)
  have hcov : Z ⊆ ⋃ x : Z, B x := fun u hu => mem_iUnion.mpr ⟨⟨u,hu⟩,mem_ball_self (hr _)⟩
  have hl : IsLindelof Z := isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨s,hs,hcover⟩ := hl.elim_countable_subcover B (fun _ => isOpen_ball) hcov
  apply measure_mono_null _ ((measure_biUnion_null_iff hs).mpr fun i _ => hz i)
  intro u hu
  obtain ⟨i,hi,hB⟩ := by simpa only [mem_iUnion,exists_prop] using hcover hu
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hB,hu⟩⟩

#print axioms analytic_zero_null
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
