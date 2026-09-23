import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOperatorCore
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularLaplacian
import GaloisForLFunctions.HTGeometry.CompactSmoothCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The full original compact modular operator core

Every smooth modular field with compact quotient support is constructed as the
full projective periodization of a compact planar test. A smooth positive orbit
normalizer retains seams and stabilizer contributions. Local finite support and
actual modular Laplacian covariance prove differential commutation. Consequently
the entire original core belongs to the native Friedrichs operator domain, is
preserved by the literal Laplacian, and has exact operator action `1-Delta_H`.
This does not assert domain admission for noncompact source fields.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

private def smoothNormalizer (w : ℂ) : ℂ :=
  w + ((1 - Real.smoothTransition (2 * w.re - 1) : ℝ) : ℂ)

private theorem smoothNormalizer_smooth : ContDiff ℝ ∞ smoothNormalizer := by
  exact contDiff_id.add (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul Complex.reCLM.contDiff).sub contDiff_const))))

private theorem smoothNormalizer_ne_zero (w : ℂ) (hw : 0 ≤ w.re) :
    smoothNormalizer w ≠ 0 := by
  have hp : 0 < (smoothNormalizer w).re := by
    change 0 < w.re + (1 - Real.smoothTransition (2 * w.re - 1))
    by_cases h : w.re ≤ 1 / 2
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
      linarith
    · have := Real.smoothTransition.le_one (2 * w.re - 1)
      linarith
  intro he
  simp only [he,Complex.zero_re,lt_self_iff_false] at hp

private theorem smoothNormalizer_eq (w : ℂ) (hw : 1 ≤ w.re) :
    smoothNormalizer w = w := by
  unfold smoothNormalizer
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp

theorem CompactChartTest.orbit_summable (g : CompactChartTest) (z : UpperHalfPlane) :
    Summable (fun γ : PSL2Z => g.field (γ • z)) := by
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z)
    (isCompact_singleton (x := z)) g.compact
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro γ hγ
  exact ⟨γ • z, ⟨z,mem_singleton z,rfl⟩,subset_tsupport g.field hγ⟩

private theorem periodize_re (g : CompactChartTest) (z : UpperHalfPlane) :
    (periodize g.field z).re = ∑' γ : PSL2Z, (g.field (γ • z)).re :=
  Complex.reCLM.map_tsum (g.orbit_summable z)

private theorem self_re_le_periodize (g : CompactChartTest)
    (hg : ∀ z, 0 ≤ (g.field z).re) (z : UpperHalfPlane) :
    (g.field z).re ≤ (periodize g.field z).re := by
  rw [periodize_re]
  simpa only [one_smul,Complex.reCLM_apply] using
    (Complex.reCLM.summable (g.orbit_summable z)).le_tsum (1 : PSL2Z)
      (fun γ _ => hg (γ • z))

/-- Every smooth field with compact quotient support is exactly a full compact
planar periodization, including all seam and stabilizer contributions. -/
theorem CoreField.exists_planar_periodization (f : CoreField) :
    ∃ g : PlanarChartTest, periodize g.toChartTest.field = f.field := by
  classical
  obtain ⟨K,hK,hfK⟩ := f.compact
  have hKU : UpperHalfPlane.coe '' K ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨z,_,rfl⟩
    exact z.im_pos
  obtain ⟨chi,W,_,hKW,hchi,hchic,hchis,hchi1⟩ :=
    HTGeometry.exists_smooth_cutoff (hK.image UpperHalfPlane.continuous_coe)
      isOpen_upperHalfPlaneSet hKU
  let b : ℂ → ℂ := fun z => (chi z : ℂ)^(2 : ℕ)
  have hb : ContDiff ℝ ∞ b := (Complex.ofRealCLM.contDiff.comp hchi).pow 2
  have hsupp : Function.support b ⊆ Function.support chi := by
    intro z hz he
    apply hz
    simp [b,he]
  have hbc : HasCompactSupport b := hchic.mono hsupp
  have hbs : tsupport b ⊆ {z : ℂ | 0 < z.im} := (closure_mono hsupp).trans hchis
  let t : CompactChartTest := CompactChartTest.ofPlanar b hb hbc hbs
  let p : UpperHalfPlane → ℂ := periodize t.field
  have ht : ∀ z : UpperHalfPlane, 0 ≤ (t.field z).re := by
    intro z
    change 0 ≤ ((chi (z:ℂ) : ℂ)^(2 : ℕ)).re
    norm_cast
    positivity
  have hp : ∀ z, 0 ≤ (p z).re := by
    intro z
    exact (ht z).trans (self_re_le_periodize t ht z)
  have hps : ChartSmooth p := periodize_smooth t.field t.compact t.smooth
  have hpi : ∀ γ : PSL2Z, ∀ z, p (γ • z) = p z := periodize_invariant t.field
  have hp1 : ∀ z, f.field z ≠ 0 → 1 ≤ (p z).re := by
    intro z hz
    obtain ⟨A,hA⟩ := exists_smul_mem_fd z
    have hi := f.invariant (QuotientGroup.mk A) z
    have hj := hpi (QuotientGroup.mk A) z
    simp only [PSL2Z_mk_smul] at hi hj
    have hAK : A • z ∈ K := by
      by_contra hn
      exact hz (hi.symm.trans (hfK (A • z) hA hn))
    have ht1 : t.field (A • z) = 1 := by
      change (chi ((A • z : UpperHalfPlane):ℂ) : ℂ)^(2 : ℕ) = 1
      rw [hchi1 _ (hKW ⟨A • z,hAK,rfl⟩)]
      norm_num
    have h := self_re_le_periodize t ht (A • z)
    change (t.field (A • z)).re ≤ (p (A • z)).re at h
    simpa only [ht1,Complex.one_re,hj] using h
  let d : UpperHalfPlane → ℂ := fun z => smoothNormalizer (p z)
  have hd : ∀ z, d z ≠ 0 := fun z => smoothNormalizer_ne_zero (p z) (hp z)
  have hds : ChartSmooth d := fun z => smoothNormalizer_smooth.contDiffAt.comp _ (hps z)
  have hdi : ∀ γ : PSL2Z, ∀ z, d (γ • z) = d z := by
    intro γ z
    dsimp [d]
    rw [hpi]
  let a : ℂ → ℂ := fun z => b z * (f.field (ofComplex z) / d (ofComplex z))
  have hac : HasCompactSupport a := hbc.mul_right
  have has : tsupport a ⊆ {z : ℂ | 0 < z.im} := tsupport_mul_subset_left.trans hbs
  have ha : ContDiff ℝ ∞ a := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : 0 < z.im
    · have hfz : ContDiffAt ℝ ∞ (f.field ∘ ofComplex) z := f.smooth ⟨z,hz⟩
      have hdz : ContDiffAt ℝ ∞ (d ∘ ofComplex) z := hds ⟨z,hz⟩
      have hinv : ContDiffAt ℝ ∞ (fun w : ℂ => (d (ofComplex w))⁻¹) z :=
        hdz.fun_inv (show (d ∘ ofComplex) z ≠ 0 from hd (ofComplex z))
      simpa only [a,Function.comp_apply,div_eq_mul_inv] using hb.contDiffAt.mul (hfz.mul hinv)
    · have hn : z ∉ tsupport b := fun h => hz (hbs h)
      apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ : ℂ => (0:ℂ))
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with w hw
      dsimp [a]
      rw [image_eq_zero_of_notMem_tsupport hw,zero_mul]
  let g : PlanarChartTest := ⟨a,ha,hac,has⟩
  refine ⟨g,?_⟩
  funext z
  change (∑' γ : PSL2Z, a ((γ • z : UpperHalfPlane):ℂ)) = f.field z
  calc
    _ = ∑' γ : PSL2Z, t.field (γ • z) * (f.field z / d z) := by
      apply tsum_congr
      intro γ
      change b ((γ • z : UpperHalfPlane):ℂ) *
        (f.field (ofComplex ((γ • z : UpperHalfPlane):ℂ)) /
          d (ofComplex ((γ • z : UpperHalfPlane):ℂ))) = _
      rw [ofComplex_apply,f.invariant,hdi]
      rfl
    _ = p z * (f.field z / d z) := tsum_mul_right
    _ = f.field z := by
      by_cases hfz : f.field z = 0
      · rw [hfz,zero_div,mul_zero]
      · have he : d z = p z := smoothNormalizer_eq _ (hp1 z hfz)
        rw [← he]
        field_simp [hd z]

/-- A constructed compact planar representative of the full original core field. -/
def CoreField.planarTest (f : CoreField) : PlanarChartTest :=
  Classical.choose f.exists_planar_periodization

theorem CoreField.planarTest_periodize (f : CoreField) :
    periodize f.planarTest.toChartTest.field = f.field :=
  Classical.choose_spec f.exists_planar_periodization

private theorem coreField_ext (f h : CoreField) (he : f.field = h.field) : f = h := by
  cases f
  cases h
  cases he
  rfl

private theorem CoreField.planarTest_coreField (f : CoreField) :
    f.planarTest.toChartTest.coreField = f :=
  coreField_ext _ _ f.planarTest_periodize

/-- Every original smooth quotient-compact field belongs to the actual native
Friedrichs operator domain, with no restriction at the modular seams. -/
theorem CoreField.mem_energyOperator_domain (f : CoreField) :
    fieldVector f ∈ energyOperator.domain := by
  have h := f.planarTest.mem_energyOperator_domain
  change fieldVector f.planarTest.toChartTest.coreField ∈ energyOperator.domain at h
  rwa [f.planarTest_coreField] at h

private theorem chartLaplacian_finite_sum {ι : Type*} (s : Finset ι)
    (f : ι → UpperHalfPlane → ℂ) (hf : ∀ i ∈ s, ChartSmooth (f i)) (z : UpperHalfPlane) :
    chartLaplacian (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, chartLaplacian (f i) z := by
  have hd (j : Fin 2) :
      fderiv ℝ (fun w => fderiv ℝ (fun v => ∑ i ∈ s, f i (ofComplex v)) w (direction j))
        (z:ℂ) (direction j) =
      ∑ i ∈ s, fderiv ℝ (fun w => fderiv ℝ (f i ∘ ofComplex) w (direction j))
        (z:ℂ) (direction j) := by
    have he : (fun w => fderiv ℝ (fun v => ∑ i ∈ s, f i (ofComplex v)) w (direction j))
        =ᶠ[𝓝 (z:ℂ)] (fun w => ∑ i ∈ s, fderiv ℝ (f i ∘ ofComplex) w (direction j)) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
      have hfi (i : ι) (hi : i ∈ s) :
          DifferentiableAt ℝ (fun v => f i (ofComplex v)) w :=
        ((hf i hi) ⟨w,hw⟩).differentiableAt (by simp)
      rw [fderiv_fun_sum (u := s) (A := fun i v => f i (ofComplex v)) hfi]
      simp only [sum_apply,Function.comp_def]
    rw [he.fderiv_eq,fderiv_fun_sum (fun i hi =>
      ((((hf i hi) z).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
        (by simp)),sum_apply]
  change (z.im:ℂ)^(2 : ℕ) * (∑ j : Fin 2,
    fderiv ℝ (fun w => fderiv ℝ (fun v => ∑ i ∈ s, f i (ofComplex v)) w (direction j))
      (z:ℂ) (direction j)) = _
  simp_rw [hd]
  rw [Finset.sum_comm,Finset.mul_sum]
  rfl

private theorem chartLaplacian_projective_pullback (γ : PSL2Z)
    (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) (z : UpperHalfPlane) :
    chartLaplacian (fun w => f (γ • w)) z = chartLaplacian f (γ • z) := by
  induction γ using QuotientGroup.induction_on with
  | H A => simpa only [PSL2Z_mk_smul] using chartLaplacian_modular_pullback A f hf z

/-- The full compact orbit sum commutes with the literal hyperbolic Laplacian. -/
theorem CompactChartTest.chartLaplacian_periodize (g : CompactChartTest) (z : UpperHalfPlane) :
    chartLaplacian (periodize g.field) z = periodize (chartLaplacian g.field) z := by
  classical
  obtain ⟨K,hK,hKz⟩ := exists_compact_mem_nhds z
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z) hK g.compact
  let s := hfin.toFinset
  have hs : ∀ᶠ w in 𝓝 z, ∀ γ ∉ s, g.field (γ • w) = 0 := by
    filter_upwards [hKz] with w hw γ hγ
    by_contra hn
    apply hγ
    exact hfin.mem_toFinset.mpr ⟨γ • w,⟨w,hw,rfl⟩,subset_tsupport g.field hn⟩
  have he : periodize g.field =ᶠ[𝓝 z] (fun w => ∑ γ ∈ s, g.field (γ • w)) := by
    filter_upwards [hs] with w hw
    exact tsum_eq_sum hw
  have hzero (γ : PSL2Z) (hγ : γ ∉ s) : chartLaplacian g.field (γ • z) = 0 := by
    rw [← chartLaplacian_projective_pullback γ g.field g.smooth]
    have hh : (fun w => g.field (γ • w)) =ᶠ[𝓝 z] (fun _ => (0:ℂ)) := by
      filter_upwards [hs] with w hw
      exact hw γ hγ
    rw [chartLaplacian_congr hh]
    simp [chartLaplacian,planarLaplacian,Function.comp_def]
  rw [chartLaplacian_congr he,
    chartLaplacian_finite_sum s _ (fun γ _ => g.smooth.modular_pullback γ)]
  simp_rw [chartLaplacian_projective_pullback _ _ g.smooth]
  exact (tsum_eq_sum hzero).symm

private theorem PlanarChartTest.chartLaplacian_field (g : PlanarChartTest) (z : UpperHalfPlane) :
    chartLaplacian g.toChartTest.field z = g.laplaceTest.toChartTest.field z := by
  have he : g.toChartTest.field ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] g.field := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
      ofComplex_apply_of_im_pos hw]
  change (z.im:ℂ)^(2 : ℕ) * D4BMModularCore.planarLaplacian (g.toChartTest.field ∘ ofComplex) (z:ℂ) =
    g.laplaceTest.field (z:ℂ)
  rw [g.laplaceTest_field]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hd : (fun w => fderiv ℝ (g.toChartTest.field ∘ ofComplex) w (direction i))
      =ᶠ[𝓝 (z:ℂ)] (fun w => fderiv ℝ g.field w (direction i)) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    rw [hw]
  rw [hd.fderiv_eq]

/-- The native Laplacian vector represents the literal Laplacian of the full
periodization, not a selected translate. -/
theorem PlanarChartTest.laplaceVector_coe (g : PlanarChartTest) :
    (g.laplaceVector : UpperHalfPlane → ℂ) =ᵐ[measure]
      chartLaplacian (periodize g.toChartTest.field) := by
  apply g.laplaceTest.toChartTest.energyTest_scalar.trans
  filter_upwards [] with z
  rw [g.toChartTest.chartLaplacian_periodize]
  apply tsum_congr
  intro γ
  exact (g.chartLaplacian_field (γ • z)).symm

/-- The exact native operator action on every original compact modular core
field is represented by its literal value minus hyperbolic Laplacian. -/
theorem CoreField.energyOperator_coe (f : CoreField) :
    (energyOperator ⟨fieldVector f,f.mem_energyOperator_domain⟩ : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => f.field z - chartLaplacian f.field z) := by
  have he : embedding f.planarTest.toChartTest.energyTest = fieldVector f :=
    congrArg fieldVector f.planarTest_coreField
  have hop : energyOperator ⟨fieldVector f,f.mem_energyOperator_domain⟩ =
      fieldVector f - f.planarTest.laplaceVector := by
    convert f.planarTest.energyOperator_apply using 1 <;> simp only [he]
  rw [hop]
  apply (Lp.coeFn_sub _ _).trans
  have hl := f.planarTest.laplaceVector_coe
  rw [f.planarTest_periodize] at hl
  exact (core_field_memLp f.field f.smooth f.compact).coeFn_toLp.sub hl

private theorem CoreField.laplacian_periodize (f : CoreField) :
    periodize f.planarTest.laplaceTest.toChartTest.field = chartLaplacian f.field := by
  funext z
  rw [← f.planarTest_periodize,f.planarTest.toChartTest.chartLaplacian_periodize]
  apply tsum_congr
  intro γ
  exact (f.planarTest.chartLaplacian_field (γ • z)).symm

/-- The literal hyperbolic Laplacian preserves the original smooth modular core. -/
def CoreField.laplacian (f : CoreField) : CoreField where
  field := chartLaplacian f.field
  smooth := f.laplacian_periodize ▸ f.planarTest.laplaceTest.toChartTest.coreField.smooth
  invariant := f.laplacian_periodize ▸ f.planarTest.laplaceTest.toChartTest.coreField.invariant
  compact := f.laplacian_periodize ▸ f.planarTest.laplaceTest.toChartTest.coreField.compact

theorem CoreField.laplacian_field (f : CoreField) :
    f.laplacian.field = chartLaplacian f.field := rfl

/-- The native closed operator has its literal differential action on the entire
original smooth compact modular core. -/
theorem CoreField.energyOperator_apply (f : CoreField) :
    energyOperator ⟨fieldVector f,f.mem_energyOperator_domain⟩ =
      fieldVector f - fieldVector f.laplacian := by
  apply Lp.ext
  apply f.energyOperator_coe.trans
  apply Filter.EventuallyEq.symm
  apply (Lp.coeFn_sub _ _).trans
  exact (core_field_memLp f.field f.smooth f.compact).coeFn_toLp.sub
    (core_field_memLp f.laplacian.field f.laplacian.smooth f.laplacian.compact).coeFn_toLp

end
end RHTower.D4BMModularCore
