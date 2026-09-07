import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMInteriorEllipticRegularity

/-!
The complete original cusp-subtracted forcing is smooth in its positive-height chart. Every compact interior localization of the actual native L² forcing vector is identified with its Schwartz representative and has every Sobolev order.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMQuadraticMixedSource GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section

/-- The complete original cusp-subtracted forcing is smooth to every spatial order. -/
theorem full_forcing_contDiffOn (q : XiZeroCopy) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (forcing q minusBranch) domain := by
  have hc : ContDiffOn ℝ ∞ (cuspResponse q minusBranch) domain := by
    unfold cuspResponse cuspPowerResponse powerResponse
    exact contDiffOn_const.mul (((contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)).add
      (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞))).add
      (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)))
  have hk : ContDiff ℝ ∞ cutoff := by
    let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
    exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      (Y.contDiff.sub contDiff_const))
  have hr : ContDiffOn ℝ ∞ (cutoffResponse q minusBranch) domain := hk.contDiffOn.mul hc
  have hl : ContDiffOn ℝ ∞ (hyperbolicLaplacian (cutoffResponse q minusBranch)) domain := by
    intro z hz
    have hf := hr.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
    have hd (i : Fin 2) : ContDiffAt ℝ ∞ (coordDeriv i (cutoffResponse q minusBranch)) z :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    have hdd (i : Fin 2) : ContDiffAt ℝ ∞
        (coordDeriv i (coordDeriv i (cutoffResponse q minusBranch))) z :=
      ((hd i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
    have hy : ContDiffAt ℝ ∞ (fun x : Fin 2 → ℝ => (x 1 : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z Y.contDiff.contDiffAt
    exact ((hy.pow 2).mul ((hdd 0).add (hdd 1))).contDiffWithinAt
  exact (contDiffOn_const.mul ((cuspLeg_contDiffOn .scalar (center q)).pow 2)).sub
    (hl.sub (contDiffOn_const.mul hr))

/-- The literal forcing expressed in the complex coordinate of the upper half-plane. -/
def forcingField (q : XiZeroCopy) (minusBranch : Bool) (z : ℂ) : ℂ :=
  forcing q minusBranch ![z.re,z.im]

/-- Spatial smoothness of the literal forcing in its original positive-height chart. -/
theorem forcingField_contDiffOn (q : XiZeroCopy) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (forcingField q minusBranch) {z : ℂ | 0 < z.im} := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  exact (full_forcing_contDiffOn q minusBranch).comp hC.contDiffOn (by intro z hz; exact hz)

/-- The full forcing localized by an actual compact interior test. -/
def InteriorTest.forcingTest (g : InteriorTest) (q : XiZeroCopy) (minusBranch : Bool) : InteriorTest where
  field z := g.field z*forcingField q minusBranch z
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport g.field
    · obtain ⟨w,hw,he⟩ := g.support hz
      have hy : 0 < z.im := he ▸ w.im_pos
      exact g.smooth.contDiffAt.mul ((forcingField_contDiffOn q minusBranch).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds hy))
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  compact := g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  support := (closure_mono (by intro z hz he; exact hz (by simp [he]))).trans g.support

private theorem native_ae_to_planar {P : ℂ → Prop}
    (hP : ∀ᵐ z : UpperHalfPlane ∂measure, P (z:ℂ)) : ∀ᵐ z ∂((volume : Measure ℂ).restrict cellChart), P z := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe measure, P z :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr hP
  rw [map_measure_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  filter_upwards [hh,ae_restrict_mem
    (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet)] with z hz hc
  apply hz
  obtain ⟨w,hw,rfl⟩ := hc
  simp [chartDensity,w.im_ne_zero]

/-- The localized L² source vector retains the original smooth forcing almost everywhere
in planar measure, after passing through the actual native density. -/
theorem InteriorTest.forcing_localValue_ae (g : InteriorTest) (q : XiZeroCopy) (minusBranch : Bool) :
    g.localValue (forcingVector q minusBranch) =ᵐ[(volume : Measure ℂ)]
      (g.forcingTest q minusBranch).field := by
  have hn := native_ae_to_planar (P := fun z : ℂ =>
    (forcingVector q minusBranch) (ofComplex z) = forcingField q minusBranch z) (by
      filter_upwards [forcingVector_coe q minusBranch] with z hz
      simpa only [ofComplex_apply,forcingField,coordinates,coe_re,coe_im] using hz)
  have hc : MeasurableSet cellChart :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet
  have he := (ae_restrict_iff' hc).mp hn
  filter_upwards [he] with z hz
  by_cases hs : z ∈ cellChart
  · simp only [InteriorTest.localValue,InteriorTest.forcingTest,hz hs]
  · have hg : g.field z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hn
      exact hs ((Set.image_mono fdo_subset_fd) (g.support hn))
    simp [InteriorTest.localValue,InteriorTest.forcingTest,hg]

/-- The actual localized full-forcing distribution has a constructed Schwartz representative. -/
theorem InteriorTest.forcing_localDistribution_eq (g : InteriorTest) (q : XiZeroCopy) (minusBranch : Bool) :
    g.localDistribution (forcingVector q minusBranch) =
      ((g.forcingTest q minusBranch).compact.toSchwartzMap
        (g.forcingTest q minusBranch).smooth : 𝓢'(ℂ,ℂ)) := by
  ext ψ
  rw [g.localDistribution_apply]
  change _ = ∫ z : ℂ, ψ z • (g.forcingTest q minusBranch).field z
  apply integral_congr_ae
  filter_upwards [g.forcing_localValue_ae q minusBranch] with z hz
  rw [hz]
  rfl

/-- Every compact localization of the actual full forcing belongs to every Sobolev order. -/
theorem full_forcing_local_sobolev (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) (s : ℝ) :
    MemSobolev s 2 (g.localDistribution (forcingVector q minusBranch)) := by
  rw [g.forcing_localDistribution_eq]
  exact SchwartzMap.memSobolev _

end
end RHTower.D4BMModularCore
