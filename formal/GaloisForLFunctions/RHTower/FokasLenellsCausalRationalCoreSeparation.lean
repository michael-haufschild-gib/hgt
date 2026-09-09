import GaloisForLFunctions.RHTower.FokasLenellsCausalFiniteBlaschke

/-! Finite rational Cauchy sums and encoded entire-core Cauchy data have trivial intersection.
Finite inner products cancel every pole, after which actual Hardy spectral-gap uniqueness applies. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual finite rational Cauchy span, embedded in the full real-line L² space. -/
def causalRationalCauchySpan : Submodule ℂ SoninL2 :=
  Submodule.span ℂ (Set.range (fun w : {z : ℂ // 0 < z.im} => (causalCauchyEigenvector w).val))

/-- The inner factor at an actual rational Cauchy pole cancels it into the upper Hardy feature. -/
theorem blaschkeMulInv_causalCauchyEigenvector (w : {z : ℂ // 0 < z.im}) :
    blaschkeMulInv w.val (causalCauchyEigenvector w).val =
      (lowerCauchyFeatureAt w.val w.property).val := by
  apply Lp.ext
  filter_upwards [coeFn_blaschkeMulInv w.val (causalCauchyEigenvector w).val,
    causalCauchyEigenvector_ae w, coe_lowerCauchyFeatureAt w.property] with x hb hp hf
  rw [hb, hp, hf]
  have hw := ofReal_sub_ne_zero w.property.ne' x
  have hc : ((starRingEnd ℂ) w.val).im ≠ 0 := by simpa using w.property.ne'
  have hcw := ofReal_sub_ne_zero hc x
  unfold blaschkeSymbolInv
  field_simp

private theorem rational_span_cancellation (u : SoninL2) (hu : u ∈ causalRationalCauchySpan) :
    ∃ ws : List {z : ℂ // 0 < z.im}, causalFiniteBlaschke ws u ∈ hardyL2 := by
  change u ∈ Submodule.span ℂ (Set.range (fun w : {z : ℂ // 0 < z.im} =>
    (causalCauchyEigenvector w).val)) at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    refine ⟨[w], ?_⟩
    change blaschkeMulInv w.val (causalCauchyEigenvector w).val ∈ hardyL2
    rw [blaschkeMulInv_causalCauchyEigenvector]
    exact (lowerCauchyFeatureAt w.val w.property).property
  | zero => exact ⟨[], hardyL2.zero_mem⟩
  | add u v _ _ ihu ihv =>
    obtain ⟨ws, hw⟩ := ihu
    obtain ⟨vs, hv⟩ := ihv
    refine ⟨ws ++ vs, ?_⟩
    rw [map_add, causalFiniteBlaschke_append, causalFiniteBlaschke_append]
    have hu' : causalFiniteBlaschke ws (causalFiniteBlaschke vs u) ∈ hardyL2 := by
      rw [causalFiniteBlaschke_commute]
      exact causalFiniteBlaschke_mem_hardy vs ⟨causalFiniteBlaschke ws u, hw⟩
    exact hardyL2.add_mem hu' (causalFiniteBlaschke_mem_hardy ws ⟨causalFiniteBlaschke vs v, hv⟩)
  | smul c u _ ihu =>
    obtain ⟨ws, hw⟩ := ihu
    refine ⟨ws, ?_⟩
    rw [map_smul]
    exact hardyL2.smul_mem c hw

/-- Every actual finite rational Cauchy sum admits a finite inner product cancelling all its poles. -/
theorem causalRationalCauchySpan_cancellation (u : causalRationalCauchySpan) :
    ∃ ws : List {z : ℂ // 0 < z.im}, causalFiniteBlaschke ws u.val ∈ hardyL2 :=
  rational_span_cancellation u.val u.property

/-- The finite rational Cauchy span and the encoded entire analytic Cauchy range intersect only at zero. -/
theorem causalRationalCauchySpan_inf_encoded_eq_bot :
    causalRationalCauchySpan ⊓ rawComplexCauchyCoreRange = ⊥ := by
  apply bot_unique
  intro f hf
  obtain ⟨hr, he⟩ := hf
  obtain ⟨u, hu⟩ := he
  change negativeCauchy u.val = f at hu
  obtain ⟨ws, hwf⟩ := causalRationalCauchySpan_cancellation ⟨f, hr⟩
  have hfLower : f ∈ hardyL2ᗮ := by
    rw [← hu]
    exact (negativeCauchy_eq_neg_iff _).1 (negativeCauchy_square u.val)
  have huf : u.val+f ∈ hardyL2 := by
    apply (negativeCauchy_eq_zero_iff _).1
    rw [map_add, hu, (negativeCauchy_eq_neg_iff f).2 hfLower, add_neg_cancel]
  have hbu : causalFiniteBlaschke ws u.val ∈ hardyL2 := by
    have h := causalFiniteBlaschke_mem_hardy ws ⟨u.val+f, huf⟩
    change causalFiniteBlaschke ws (u.val+f) ∈ hardyL2 at h
    rw [map_add] at h
    simpa only [add_sub_cancel_right] using hardyL2.sub_mem h hwf
  obtain ⟨b, hg⟩ := causalFiniteBlaschke_core_zeroGap ws u
  have hz := (upperHardyL2_gap_zero_iff ⟨causalFiniteBlaschke ws u.val, hbu⟩ 0 b).1 hg
  have hv : causalFiniteBlaschke ws u.val = 0 := congrArg (fun v : UpperHardyL2 => v.val) hz
  have hn := norm_causalFiniteBlaschke ws u.val
  rw [hv, norm_zero] at hn
  have hu0 : u.val = 0 := norm_eq_zero.mp hn.symm
  rw [hu0, map_zero] at hu
  exact hu.symm

end
end RHTower.FokasLenells
