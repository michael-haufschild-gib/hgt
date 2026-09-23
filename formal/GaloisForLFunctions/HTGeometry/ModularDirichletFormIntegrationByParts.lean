import GaloisForLFunctions.HTGeometry.ModularDirichletFormDomain

/-!
# Integration by parts on the modular fundamental domain against interior test functions

For a `C¹` function `u` on `ℍ` and a `C¹` test function `φ : ℂ → ℂ` with compact support inside the
image of the interior `𝒟°` of the fundamental domain, the hyperbolic gradient components pair
with `y φ` as

`∫_𝒟 y φ · (y ∂_x u) dμ = − ∫_𝒟 y · (y ∂_x φ) · u dμ`,

and likewise for `∂_y`: in the chart the hyperbolic measure is `dx dy / y²`, so both sides are
Euclidean integrals `∫ φ ∂_x f = −∫ (∂_x φ) f` over `ℂ` of compactly supported continuous
integrands, and the boundary of `𝒟` is never seen.  This is the identity by which the closure of
the modular Dirichlet form is identified: it makes the pairing with interior test functions a
continuous functional on `L²(𝒟)³` vanishing on the embedded pre-domain.
-/

open UpperHalfPlane MeasureTheory ModularGroup Set Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The chart of the fundamental domain -/

/-- The image in `ℂ` of the interior of the fundamental domain. -/
def fdoImage : Set ℂ := UpperHalfPlane.coe '' fdo

theorem isOpen_fdoImage : IsOpen fdoImage := isOpenEmbedding_coe.isOpenMap _ isOpen_fdo

theorem fdoImage_subset_upperSet : fdoImage ⊆ upperSet := by
  rintro w ⟨z, _, rfl⟩
  exact z.im_pos

theorem fdoImage_subset_coe_image_fd : fdoImage ⊆ UpperHalfPlane.coe '' fd :=
  Set.image_mono fdo_subset_fd

theorem measurableSet_coe_image_fd : MeasurableSet (UpperHalfPlane.coe '' fd) :=
  measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet

/-- **The fundamental-domain integral in the chart:** `∫_𝒟 F dμ = ∫_{𝒟 ⊆ ℂ} y⁻² F(x+iy) dx dy`. -/
theorem setIntegral_fd_eq_chart (F : ℍ → ℂ) :
    ∫ z in fd, F z ∂volume =
      ∫ w in UpperHalfPlane.coe '' fd, ((w.im ^ (2 : ℕ))⁻¹ : ℝ) • F (ofComplex w) ∂volume := by
  rw [volume_eq_comap_withDensity,
    setIntegral_withDensity_eq_setIntegral_toReal_smul measurable_hyperbolicDensity
      (ae_of_all _ fun z => hyperbolicDensity_lt_top z) F isClosed_fd.measurableSet]
  have h2 := measurePreserving_coe.setIntegral_image_emb measurableEmbedding_coe
    (fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w)) fd
  simp only [ofComplex_apply] at h2
  rw [← h2, Measure.restrict_restrict measurableSet_coe_image_fd,
    inter_eq_self_of_subset_left (image_subset_range _ _)]
  refine setIntegral_congr_fun measurableSet_coe_image_fd fun w hw => ?_
  obtain ⟨z, _, rfl⟩ := hw
  rw [ofComplex_apply, hyperbolicDensity_toReal]
  rfl

/-- A function supported inside `𝒟°` integrates over `𝒟 ⊆ ℂ` as over `ℂ`. -/
theorem setIntegral_coe_image_fd_eq_integral (G : ℂ → ℂ) (hG : ∀ w ∉ fdoImage, G w = 0) :
    ∫ w in UpperHalfPlane.coe '' fd, G w ∂volume = ∫ w, G w ∂volume :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
    hG w (fun h => hw (fdoImage_subset_coe_image_fd h))

/-! ## Continuity and integrability of the chart integrands -/

/-- A `C¹` chart function times a test function supported in `𝒟°` is continuous on `ℂ`. -/
theorem continuous_mul_of_tsupport_subset {f g : ℂ → ℂ} (hf : ContinuousOn f upperSet)
    (hg : Continuous g) (hU : tsupport g ⊆ fdoImage) : Continuous fun w => f w * g w := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w ∈ upperSet
  · exact ((hf w hw).continuousAt (isOpen_upperSet.mem_nhds hw)).mul hg.continuousAt
  · have hnot : w ∉ tsupport g := fun h => hw (fdoImage_subset_upperSet (hU h))
    have hmem : (tsupport g)ᶜ ∈ nhds w := (isClosed_tsupport g).isOpen_compl.mem_nhds hnot
    have hev : (fun w => f w * g w) =ᶠ[nhds w] fun _ => 0 := by
      filter_upwards [hmem] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    exact hev.continuousAt

theorem integrable_mul_of_tsupport_subset {f g : ℂ → ℂ} (hf : ContinuousOn f upperSet)
    (hg : Continuous g) (hgs : HasCompactSupport g) (hU : tsupport g ⊆ fdoImage) :
    Integrable (fun w => f w * g w) volume :=
  (continuous_mul_of_tsupport_subset hf hg hU).integrable_of_hasCompactSupport (hgs.mul_left)

/-! ## The chart derivative of a pre-domain element -/

theorem IsChartC1.continuousOn {u : ℍ → ℂ} (hu : IsChartC1 u) : ContinuousOn (chartFun u) upperSet :=
  ContDiffOn.continuousOn hu

theorem IsChartC1.continuousOn_fderiv {u : ℍ → ℂ} (hu : IsChartC1 u) (v : ℂ) :
    ContinuousOn (fun w => fderiv ℝ (chartFun u) w v) upperSet := by
  have h := ContDiffOn.continuousOn_fderiv_of_isOpen hu isOpen_upperSet le_rfl
  exact h.clm_apply continuousOn_const

theorem hypGradX_ofComplex {u : ℍ → ℂ} {w : ℂ} (hw : w ∈ upperSet) :
    hypGradX u (ofComplex w) = (w.im : ℂ) * fderiv ℝ (chartFun u) w 1 := by
  unfold hypGradX chartDeriv
  rw [ofComplex_apply_of_im_pos hw]
  rfl

theorem hypGradY_ofComplex {u : ℍ → ℂ} {w : ℂ} (hw : w ∈ upperSet) :
    hypGradY u (ofComplex w) = (w.im : ℂ) * fderiv ℝ (chartFun u) w Complex.I := by
  unfold hypGradY chartDeriv
  rw [ofComplex_apply_of_im_pos hw]
  rfl

theorem chartFun_ofComplex (u : ℍ → ℂ) (w : ℂ) : u (ofComplex w) = chartFun u w := rfl

/-! ## Integration by parts -/

/-- **Integration by parts against an interior test function**, directional version: for a `C¹`
function `u` on `ℍ`, a direction `v` and a `C¹` test function `φ` with compact support in `𝒟°`,
`∫_𝒟 y φ · (y ∂_v u) dμ = − ∫_𝒟 y · (y ∂_v φ) · u dμ`. -/
theorem setIntegral_fd_testWeight_chartDeriv {u : ℍ → ℂ} (hu : IsChartC1 u) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hU : tsupport φ ⊆ fdoImage) (v : ℂ) :
    ∫ z in fd, (z.im : ℂ) * φ z * ((z.im : ℂ) * chartDeriv u v z) ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z v) * u z ∂volume := by
  set f := chartFun u with hf
  -- continuity of the four factors
  have hfc : ContinuousOn f upperSet := hu.continuousOn
  have hf'c : ContinuousOn (fun w => fderiv ℝ f w v) upperSet := hu.continuousOn_fderiv v
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous fun w => fderiv ℝ φ w v :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- the support of the derivative of the test function
  have hsupp' : Function.support (fun w => fderiv ℝ φ w v) ⊆ tsupport φ := by
    intro w hw
    by_contra hcon
    apply hw
    have h0 : φ =ᶠ[nhds w] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hcon] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    show fderiv ℝ φ w v = 0
    rw [h0.fderiv_eq, fderiv_const_apply]
    rfl
  have hts' : tsupport (fun w => fderiv ℝ φ w v) ⊆ tsupport φ :=
    closure_minimal hsupp' (isClosed_tsupport φ)
  have hs' : HasCompactSupport fun w => fderiv ℝ φ w v :=
    hs.of_isClosed_subset (isClosed_tsupport _) hts'
  have hU' : tsupport (fun w => fderiv ℝ φ w v) ⊆ fdoImage := hts'.trans hU
  -- the chart integrands
  have hL : ∫ z in fd, (z.im : ℂ) * φ z * ((z.im : ℂ) * chartDeriv u v z) ∂volume =
      ∫ w, φ w * fderiv ℝ f w v ∂volume := by
    rw [setIntegral_fd_eq_chart]
    rw [← setIntegral_coe_image_fd_eq_integral (fun w => φ w * fderiv ℝ f w v)
      (fun w hw => by rw [image_eq_zero_of_notMem_tsupport (fun h => hw (hU h)), zero_mul])]
    refine setIntegral_congr_fun measurableSet_coe_image_fd fun w hw => ?_
    have hw' : w ∈ upperSet := by
      obtain ⟨z, _, rfl⟩ := hw
      exact z.im_pos
    have hy : (w.im : ℂ) ≠ 0 := by
      have : (0 : ℝ) < w.im := hw'
      exact_mod_cast this.ne'
    simp only [ofComplex_apply_of_im_pos hw']
    show ((w.im ^ (2 : ℕ))⁻¹ : ℝ) • ((w.im : ℂ) * φ w * ((w.im : ℂ) * fderiv ℝ f w v)) =
      φ w * fderiv ℝ f w v
    rw [Complex.real_smul]
    push_cast
    field_simp
  have hR : ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z v) * u z ∂volume =
      ∫ w, fderiv ℝ φ w v * f w ∂volume := by
    rw [setIntegral_fd_eq_chart]
    rw [← setIntegral_coe_image_fd_eq_integral (fun w => fderiv ℝ φ w v * f w)
      (fun w hw => by rw [image_eq_zero_of_notMem_tsupport (fun h => hw (hU' h)), zero_mul])]
    refine setIntegral_congr_fun measurableSet_coe_image_fd fun w hw => ?_
    have hw' : w ∈ upperSet := by
      obtain ⟨z, _, rfl⟩ := hw
      exact z.im_pos
    have hy : (w.im : ℂ) ≠ 0 := by
      have : (0 : ℝ) < w.im := hw'
      exact_mod_cast this.ne'
    simp only [ofComplex_apply_of_im_pos hw']
    have hfw : f w = u ⟨w, hw'⟩ := by
      rw [hf]
      show u (ofComplex w) = u ⟨w, hw'⟩
      rw [ofComplex_apply_of_im_pos hw']
    show ((w.im ^ (2 : ℕ))⁻¹ : ℝ) • ((w.im : ℂ) * ((w.im : ℂ) * fderiv ℝ φ w v) * u ⟨w, hw'⟩) =
      fderiv ℝ φ w v * f w
    rw [hfw, Complex.real_smul]
    push_cast
    field_simp
  rw [hL, hR]
  -- integration by parts on `ℂ`
  have h1 : Integrable (fun w => fderiv ℝ φ w v * f w) volume :=
    (integrable_mul_of_tsupport_subset hfc hφ'c hs' hU').congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have h2 : Integrable (fun w => φ w * fderiv ℝ f w v) volume :=
    (integrable_mul_of_tsupport_subset hf'c hφc hs hU).congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have h3 : Integrable (fun w => φ w * f w) volume :=
    (integrable_mul_of_tsupport_subset hfc hφc hs hU).congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun w _ => (hφ.differentiable one_ne_zero) w) (fun w hw => ?_)
  have hw' : w ∈ upperSet := fdoImage_subset_upperSet (hU hw)
  exact (ContDiffOn.differentiableOn hu one_ne_zero).differentiableAt
    (isOpen_upperSet.mem_nhds hw')

/-- The `∂_x` form of the integration by parts, in terms of the hyperbolic gradient. -/
theorem setIntegral_fd_testWeight_hypGradX {u : ℍ → ℂ} (hu : IsChartC1 u) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hU : tsupport φ ⊆ fdoImage) :
    ∫ z in fd, (z.im : ℂ) * φ z * hypGradX u z ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z 1) * u z ∂volume :=
  setIntegral_fd_testWeight_chartDeriv hu hφ hs hU 1

/-- The `∂_y` form of the integration by parts, in terms of the hyperbolic gradient. -/
theorem setIntegral_fd_testWeight_hypGradY {u : ℍ → ℂ} (hu : IsChartC1 u) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hU : tsupport φ ⊆ fdoImage) :
    ∫ z in fd, (z.im : ℂ) * φ z * hypGradY u z ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z Complex.I) * u z ∂volume :=
  setIntegral_fd_testWeight_chartDeriv hu hφ hs hU Complex.I

end

end GaloisForLFunctions.HTGeometry
