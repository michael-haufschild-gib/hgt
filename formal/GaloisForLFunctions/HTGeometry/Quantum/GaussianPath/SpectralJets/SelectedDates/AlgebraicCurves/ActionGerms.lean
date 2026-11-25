import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.RealSlice

/-! # Algebraic normalized actions and their nonconstant real restrictions -/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- A complex linear combination of algebraic energy germs divided by
a gap remains algebraic over the rational functions of the line. -/
theorem ratio_germ_algebraic {I : Type*} [Fintype I] (f : I → ℂ → ℂ)
    (hf : ∀ i, MeromorphicAt (f i) 0) (ha : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (f i) (hf i)))
    (c : I → ℂ) (i j : I)
    (hg : MeromorphicAt (fun z => (∑ l, c l*f l z)*(f i z-f j z)⁻¹) 0) :
    IsAlgebraic (RatFunc ℂ) (ofMero _ hg) := by
  let g (l : I) (z : ℂ) := c l*f l z
  have hm (l : I) : MeromorphicAt (g l) 0 := (MeromorphicAt.const (c l) 0).mul (hf l)
  have hs : MeromorphicAt (fun z => ∑ l, g l z) 0 := by
    exact MeromorphicAt.fun_sum (fun l _ => hm l)
  let K := (algebraicClosure (RatFunc ℂ) MeroGerm).restrictScalars ℂ
  have hmem (l : I) : ofMero (f l) (hf l)∈K := mem_algebraicClosure_iff.mpr (ha l)
  have hc (l : I) : ofMero (g l) (hm l)∈K := by
    have hmul := K.mul_mem (K.algebraMap_mem (c l)) (hmem l)
    rw [algebraMap_complex_meroGerm,ofMero_mul] at hmul
    exact hmul
  have hsum := K.sum_mem (t:=Finset.univ) fun l _ => hc l
  rw [sum_germs g hm hs] at hsum
  have hd := K.inv_mem (K.sub_mem (hmem i) (hmem j))
  rw [ofMero_sub,ofMero_inv] at hd
  have hprod := K.mul_mem hsum hd
  rw [ofMero_mul] at hprod
  exact mem_algebraicClosure_iff.mp hprod

/-- If the real restriction continues analytically along a segment and
takes distinct endpoint values, its complex germ cannot be constant. -/
theorem nonconstant_of_segment {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {F : ℝ → ℂ}
    (hF : AnalyticOnNhd ℝ F (Icc 0 1)) (hline : (fun t : ℝ => f t) =ᶠ[𝓝 0] F)
    (hend : F 0≠F 1) (c : ℂ) : ¬(f =ᶠ[𝓝[≠] 0] fun _ => c) := by
  intro he
  have hu : f =ᶠ[𝓝 0] fun _ => c :=
    (hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp he
  have ht : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝 0) (𝓝 0) := by simpa using Complex.continuous_ofReal.tendsto 0
  have hg : F =ᶠ[𝓝 0] fun _ => c := hline.symm.trans (hu.comp_tendsto ht)
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_Icc (left_mem_Icc.mpr zero_le_one) hg
  exact hend ((hall (left_mem_Icc.mpr zero_le_one)).trans (hall (right_mem_Icc.mpr zero_le_one)).symm)

#print axioms ratio_germ_algebraic
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
