import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart
import GaloisForLFunctions.RHTower.EisensteinLineSourceIntegrability
import GaloisForLFunctions.HTGeometry.ModularDirichletFormIntegrationByParts

/-!
# Integrability on the fundamental domain from power majorants

`IntegrableOn g 𝒟` is transported to the chart through the hyperbolic density and the measurable
embedding `ℍ → ℂ`; a function bounded by `C · y^β` on `𝒟` with `β < 1` is integrable on `𝒟`,
because `y^{β−2}` is integrable on the rectangle `[−½, ½] × [√3/2, ∞)` containing the chart of `𝒟`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature (fullDomain_iff_fd)
open GaloisForLFunctions.RHTower.SelbergMaassStripGap (rectangle rectangle_measurable)
open GaloisForLFunctions.RHTower.SelbergModularDomainSlices (arcFloor arcFloor_pos)
open GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget (fullDomain fullDomain_measurable)

namespace RHTower

noncomputable section

theorem indicator_fd_eq_comp (g : ℍ → ℂ) :
    fd.indicator g =
      (fun w : ℂ => (UpperHalfPlane.coe '' fd).indicator (fun w => g (ofComplex w)) w) ∘
        UpperHalfPlane.coe := by
  funext z
  simp only [Function.comp_apply]
  by_cases hz : z ∈ fd
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (Set.mem_image_of_mem _ hz),
      ofComplex_apply]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
    rintro ⟨w, hw, hwz⟩
    exact hz (UpperHalfPlane.coe_injective hwz ▸ hw)

theorem coe_image_fd_subset_upper : UpperHalfPlane.coe '' fd ⊆ {w : ℂ | 0 < w.im} := by
  rintro w ⟨z, _, rfl⟩
  exact z.im_pos

/-- **Integrability on `𝒟` in the chart.** -/
theorem integrableOn_fd_iff_chart (g : ℍ → ℂ) :
    IntegrableOn g fd volume ↔
      IntegrableOn (fun w : ℂ => ((chartDensity w : NNReal) : ℝ) • g (ofComplex w))
        (UpperHalfPlane.coe '' fd) volume := by
  have hm : Measurable chartDensity := by unfold chartDensity; fun_prop
  rw [← integrable_indicator_iff isClosed_fd.measurableSet, indicator_fd_eq_comp,
    ← UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff, map_volume_chart,
    integrable_withDensity_iff_integrable_coe_smul hm,
    ← integrable_indicator_iff measurableSet_coe_image_fd, Set.indicator_smul]
  constructor
  · intro h
    have hsupp : Function.support (fun w : ℂ => ((chartDensity w : NNReal) : ℝ) •
        (UpperHalfPlane.coe '' fd).indicator (fun w => g (ofComplex w)) w) ⊆ {w : ℂ | 0 < w.im} := by
      intro w hw
      apply coe_image_fd_subset_upper
      by_contra hnot
      apply hw
      simp [Set.indicator_of_notMem hnot]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp h
  · intro h
    exact h.integrableOn

/-- `y^{β−2}` is integrable on the rectangle. -/
theorem integrableOn_rpow_rectangle {β : ℝ} (hβ : β < 1) :
    IntegrableOn (fun p : ℝ × ℝ => ((p.2 ^ (β - 2) : ℝ) : ℂ)) rectangle := by
  have hy : Integrable (fun y : ℝ => ((y ^ (β - 2) : ℝ) : ℂ))
      (volume.restrict (Ici arcFloor)) := by
    have h : IntegrableOn (fun y : ℝ => y ^ (β - 2)) (Ioi arcFloor) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) arcFloor_pos
    rw [← integrableOn_Ici_iff_integrableOn_Ioi] at h
    exact h.ofReal
  have h := hy.comp_snd (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2)))
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

/-- **Power majorants are integrable on `𝒟`.** -/
theorem integrableOn_fd_rpow {β : ℝ} (hβ : β < 1) :
    IntegrableOn (fun z : ℍ => ((z.im ^ β : ℝ) : ℂ)) fd volume := by
  rw [integrableOn_fd_iff_chart]
  let G' : ℝ × ℝ → ℂ := fun p => ((p.2 ^ (β - 2) : ℝ) : ℂ)
  have hG' : IntegrableOn G' fullDomain :=
    (integrableOn_rpow_rectangle hβ).mono_set fullDomain_subset_rectangle
  have hpre : IntegrableOn (G' ∘ Complex.measurableEquivRealProd)
      (Complex.measurableEquivRealProd ⁻¹' fullDomain) volume :=
    ((Complex.volume_preserving_equiv_real_prod.restrict_preimage fullDomain_measurable).integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hG'
  have hsub : UpperHalfPlane.coe '' fd ⊆ Complex.measurableEquivRealProd ⁻¹' fullDomain := by
    rintro w ⟨z, hz, rfl⟩
    show Complex.measurableEquivRealProd (z : ℂ) ∈ fullDomain
    rw [Complex.measurableEquivRealProd_apply]
    exact (fullDomain_iff_fd z).mpr hz
  refine (hpre.mono_set hsub).congr_fun (fun w hw => ?_) measurableSet_coe_image_fd
  obtain ⟨z, _, rfl⟩ := hw
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, G', ofComplex_apply,
    chartDensity, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos z.im_pos, Complex.real_smul, UpperHalfPlane.coe_im]
  rw [Real.rpow_sub z.im_pos, Real.rpow_two]
  push_cast
  field_simp

/-- **Integrability on `𝒟` from a power bound**: `‖g z‖ ≤ C y^β` on `𝒟` with `β < 1`. -/
theorem integrableOn_fd_of_norm_le {g : ℍ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict fd))
    {β C : ℝ} (hβ : β < 1) (hC : ∀ z ∈ fd, ‖g z‖ ≤ C * z.im ^ β) :
    IntegrableOn g fd volume := by
  have hmaj : IntegrableOn (fun z : ℍ => C * z.im ^ β) fd volume := by
    have h : IntegrableOn (fun z : ℍ => C * ‖((z.im ^ β : ℝ) : ℂ)‖) fd volume :=
      (integrableOn_fd_rpow hβ).norm.const_mul C
    refine h.congr_fun (fun z _ => ?_) isClosed_fd.measurableSet
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg z.im_pos.le β)]
  refine Integrable.mono' hmaj hg ?_
  exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall hC)

/-- Constants are integrable on `𝒟`. -/
theorem integrableOn_fd_const (c : ℂ) : IntegrableOn (fun _ : ℍ => c) fd volume :=
  integrableOn_const (by simp [volume_fd_ne_top])


/-! ## The general coordinate version -/

theorem indicator_coord_eq_comp {S : Set ℍ} (g : ℍ → ℂ) :
    S.indicator g =
      (fun w : ℂ => (UpperHalfPlane.coe '' S).indicator (fun w => g (ofComplex w)) w) ∘
        UpperHalfPlane.coe := by
  funext z
  simp only [Function.comp_apply]
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (Set.mem_image_of_mem _ hz),
      ofComplex_apply]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
    rintro ⟨w, hw, hwz⟩
    exact hz (UpperHalfPlane.coe_injective hwz ▸ hw)

theorem coe_image_subset_upper (S : Set ℍ) : UpperHalfPlane.coe '' S ⊆ {w : ℂ | 0 < w.im} := by
  rintro w ⟨z, _, rfl⟩
  exact z.im_pos

/-- **Integrability on a measurable subset of `ℍ` in the chart.** -/
theorem integrableOn_iff_chart {S : Set ℍ} (hS : MeasurableSet S) (g : ℍ → ℂ) :
    IntegrableOn g S volume ↔
      IntegrableOn (fun w : ℂ => ((chartDensity w : NNReal) : ℝ) • g (ofComplex w))
        (UpperHalfPlane.coe '' S) volume := by
  have hm : Measurable chartDensity := by unfold chartDensity; fun_prop
  have hSc : MeasurableSet (UpperHalfPlane.coe '' S) :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hS
  rw [← integrable_indicator_iff hS, indicator_coord_eq_comp,
    ← UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff, map_volume_chart,
    integrable_withDensity_iff_integrable_coe_smul hm,
    ← integrable_indicator_iff hSc, Set.indicator_smul]
  constructor
  · intro h
    have hsupp : Function.support (fun w : ℂ => ((chartDensity w : NNReal) : ℝ) •
        (UpperHalfPlane.coe '' S).indicator (fun w => g (ofComplex w)) w) ⊆ {w : ℂ | 0 < w.im} := by
      intro w hw
      apply coe_image_subset_upper S
      by_contra hnot
      apply hw
      simp [Set.indicator_of_notMem hnot]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp h
  · intro h
    exact h.integrableOn

/-- Transport to `ℝ × ℝ`: integrability on `{(Re, Im) ∈ A}` is integrability of `F/y²` on `A`. -/
theorem integrableOn_coord_iff {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, 0 < p.2) (F : ℝ × ℝ → ℂ) :
    IntegrableOn (fun z : ℍ => F (z.re, z.im)) {z : ℍ | (z.re, z.im) ∈ A} volume ↔
      IntegrableOn (fun p : ℝ × ℝ => F p / ((p.2 : ℝ) : ℂ) ^ 2) A volume := by
  have hS : MeasurableSet {z : ℍ | (z.re, z.im) ∈ A} := measurable_coordMap hA
  rw [integrableOn_iff_chart hS]
  have himage : UpperHalfPlane.coe '' {z : ℍ | (z.re, z.im) ∈ A} =
      Complex.measurableEquivRealProd ⁻¹' A := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show Complex.measurableEquivRealProd (z : ℂ) ∈ A
      rw [Complex.measurableEquivRealProd_apply]
      exact hz
    · intro hw
      have hw' : (w.re, w.im) ∈ A := by
        simpa [Complex.measurableEquivRealProd_apply] using hw
      have hwim : 0 < w.im := hpos _ hw'
      refine ⟨ofComplex w, ?_, ?_⟩
      · show ((ofComplex w).re, (ofComplex w).im) ∈ A
        rw [ofComplex_apply_of_im_pos hwim]
        exact hw'
      · exact ofComplex_apply_of_im_pos hwim ▸ rfl
  rw [himage]
  have hchart : ∀ w ∈ Complex.measurableEquivRealProd ⁻¹' A,
      ((chartDensity w : NNReal) : ℝ) • F ((ofComplex w).re, (ofComplex w).im) =
        (fun p : ℝ × ℝ => F p / ((p.2 : ℝ) : ℂ) ^ 2) (Complex.measurableEquivRealProd w) := by
    intro w hw
    have hw' : (w.re, w.im) ∈ A := by
      simpa [Complex.measurableEquivRealProd_apply] using hw
    have hwim : 0 < w.im := hpos _ hw'
    have hre : (ofComplex w).re = w.re := by rw [ofComplex_apply_of_im_pos hwim]; rfl
    have him : (ofComplex w).im = w.im := by rw [ofComplex_apply_of_im_pos hwim]; rfl
    simp only [Complex.measurableEquivRealProd_apply, hre, him,
      chartDensity, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos hwim, Complex.real_smul]
    have hne : ((w.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwim.ne'
    push_cast
    field_simp
  have hiff := integrableOn_congr_fun (μ := volume)
    (f := fun w : ℂ => ((chartDensity w : NNReal) : ℝ) • F ((ofComplex w).re, (ofComplex w).im))
    (g := fun w : ℂ => (fun p : ℝ × ℝ => F p / ((p.2 : ℝ) : ℂ) ^ 2)
      (Complex.measurableEquivRealProd w))
    hchart (hA.preimage Complex.measurableEquivRealProd.measurable)
  rw [hiff]
  exact (Complex.volume_preserving_equiv_real_prod.restrict_preimage hA).integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (g := fun p : ℝ × ℝ => F p / ((p.2 : ℝ) : ℂ) ^ 2)

end

end RHTower
