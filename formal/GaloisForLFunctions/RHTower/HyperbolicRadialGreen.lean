import GaloisForLFunctions.RHTower.HyperbolicKernelIntegral

/-!
# The Green identity on the upper half-plane against radial kernels

The invariant integral is `∫_ℍ F dμ = ∫_{Im w > 0} (Im w)⁻² F(w) dw`.  For a `C²` profile `φ`
vanishing beyond `R`, the test `ζ ↦ φ(U(ζ, z))` (extended by zero) is `C²` on `ℂ` with compact
support inside the upper half-plane, and its planar Laplacian is `(Im ζ)⁻² Dφ(U(ζ, z))`.  Two
integrations by parts in the plane therefore give, for every `C²` function `V` on `ℍ`,

  `∫_ℍ φ(u(z, w)) y²ΔV(w) dμ(w) = ∫_ℍ Dφ(u(z, w)) V(w) dμ(w)`,

with `y²Δ = y²(∂ₓ² + ∂ᵧ²)` the Laplace–Beltrami operator and `Dφ(u) = u(u+1)φ''(u) + (2u+1)φ'(u)`.
Vector-valued `V` reduce to real-valued ones through continuous linear functionals.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.DeckPointPair

open GaloisForLFunctions.HTGeometry SelbergMaassTraceEnergy SelbergLocalTestGreen

noncomputable section

/-- **The invariant integral in the chart**: `∫_ℍ F dμ = ∫_{Im w > 0} (Im w)⁻² F(w) dw`. -/
theorem integral_eq_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℍ → E) :
    ∫ z, F z = ∫ w in {w : ℂ | 0 < w.im}, ((w.im ^ 2)⁻¹ : ℝ) • F (ofComplex w) := by
  rw [volume_eq_comap_withDensity, integral_withDensity_eq_integral_toReal_smul
    measurable_hyperbolicDensity (ae_of_all _ fun z => hyperbolicDensity_lt_top z)]
  have h2 := measurePreserving_coe.integral_comp measurableEmbedding_coe
    (fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w))
  simp only [ofComplex_apply] at h2
  rw [h2, range_coe]
  refine setIntegral_congr_fun (isOpen_lt continuous_const Complex.continuous_im).measurableSet
    fun w hw => ?_
  rw [hyperbolicDensity_toReal, ofComplex_apply_of_im_pos hw]
  rfl

/-! ## The radial test function -/

/-- The test `ζ ↦ φ(U(ζ, z))` on the upper half-plane, extended by zero. -/
def radialTest (φ : ℝ → ℝ) (z : ℍ) (ζ : ℂ) : ℝ := if 0 < ζ.im then φ (pairUc ζ z) else 0

theorem radialTest_of_im_pos (φ : ℝ → ℝ) (z : ℍ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    radialTest φ z ζ = φ (pairUc ζ z) := if_pos hζ

theorem contDiffOn_pairUc_left (z : ℍ) :
    ContDiffOn ℝ ∞ (fun ζ : ℂ => pairUc ζ z) {ζ : ℂ | 0 < ζ.im} := by
  have hz := z.im_pos
  have hre : ContDiff ℝ ∞ (fun ζ : ℂ => ζ.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun ζ : ℂ => ζ.im) := Complex.imCLM.contDiff
  have hnum : ContDiff ℝ ∞ (fun ζ : ℂ => (ζ.re - z.re) ^ 2 + (ζ.im - z.im) ^ 2) :=
    ((hre.sub contDiff_const).pow 2).add ((him.sub contDiff_const).pow 2)
  have hden : ContDiff ℝ ∞ (fun ζ : ℂ => 4 * ζ.im * z.im) :=
    (contDiff_const.mul him).mul contDiff_const
  exact hnum.contDiffOn.div hden.contDiffOn fun ζ hζ => by
    have : 0 < ζ.im := hζ
    positivity

section Test

variable {φ : ℝ → ℝ} {R : ℝ} (hφ : ContDiff ℝ 2 φ) (hR : 0 ≤ R) (hφR : KernelSupport φ R)

include hR hφR in
theorem radialTest_eq_zero_of_im_lt (z : ℍ) {ζ : ℂ} (h : ζ.im < z.im / (4 * R + 2)) :
    radialTest φ z ζ = 0 := by
  unfold radialTest
  split_ifs with hζ
  · refine hφR _ ?_
    by_contra hle
    obtain ⟨-, h2, -⟩ := pairUc_le_bounds hζ (not_lt.1 hle)
    rw [lt_div_iff₀ (by linarith)] at h
    linarith
  · rfl

include hφ hR hφR in
theorem contDiff_radialTest (z : ℍ) : ContDiff ℝ 2 (radialTest φ z) := by
  rw [contDiff_iff_contDiffAt]
  intro ζ
  by_cases hζ : 0 < ζ.im
  · have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
    have hc : ContDiffAt ℝ 2 (fun ζ : ℂ => φ (pairUc ζ z)) ζ :=
      hφ.contDiffAt.comp ζ (((contDiffOn_pairUc_left z).of_le (by norm_cast))
        |>.contDiffAt (hopen.mem_nhds hζ))
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hζ] with ζ' hζ'
    exact radialTest_of_im_pos φ z hζ'
  · have hz : 0 < z.im / (4 * R + 2) := div_pos z.im_pos (by linarith)
    have hopen : IsOpen {ζ : ℂ | ζ.im < z.im / (4 * R + 2)} :=
      isOpen_lt Complex.continuous_im continuous_const
    refine contDiffAt_const (c := (0 : ℝ)) |>.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds (show ζ.im < z.im / (4 * R + 2) by linarith)] with ζ' hζ'
    exact radialTest_eq_zero_of_im_lt hR hφR z hζ'

include hR hφR in
theorem radialTest_eq_zero_of_not_mem (z : ℍ) {ζ : ℂ}
    (h : ζ ∉ Metric.closedBall (z : ℂ) (2 * ((4 * R + 2) * z.im)) ∩
      {ζ : ℂ | z.im / (4 * R + 2) ≤ ζ.im}) : radialTest φ z ζ = 0 := by
  unfold radialTest
  split_ifs with hζ
  · refine hφR _ ?_
    by_contra hle
    obtain ⟨h1, h2, h3⟩ := pairUc_le_bounds hζ (not_lt.1 hle)
    have hz := z.im_pos
    apply h
    have hζz : ζ.im ≤ (4 * R + 2) * z.im := by
      rw [div_le_iff₀ (by linarith)] at h1; linarith
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hre : |ζ.re - z.re| ≤ (4 * R + 2) * z.im := by
        apply abs_le_of_sq_le_sq' _ (by positivity) |>.elim (fun a b => abs_le.2 ⟨a, b⟩)
        have : 4 * R * ζ.im * z.im ≤ ((4 * R + 2) * z.im) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hζz (by positivity : (0 : ℝ) ≤ 4 * R * z.im)
          nlinarith
        simpa using h3.trans this
      have him : |ζ.im - z.im| ≤ (4 * R + 2) * z.im := by
        rw [abs_le]; constructor <;> nlinarith
      calc ‖ζ - (z : ℂ)‖ ≤ |(ζ - (z : ℂ)).re| + |(ζ - (z : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 2 * ((4 * R + 2) * z.im) := by
          simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
          linarith
    · show z.im / (4 * R + 2) ≤ ζ.im
      rw [div_le_iff₀ (by linarith)]
      linarith
  · rfl

include hR hφR in
theorem hasCompactSupport_radialTest (z : ℍ) : HasCompactSupport (radialTest φ z) :=
  HasCompactSupport.intro ((isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im))
    fun _ hζ => radialTest_eq_zero_of_not_mem hR hφR z hζ

include hR hφR in
theorem tsupport_radialTest_subset (z : ℍ) :
    tsupport (radialTest φ z) ⊆ {ζ : ℂ | 0 < ζ.im} := by
  have hz : 0 < z.im / (4 * R + 2) := div_pos z.im_pos (by linarith)
  refine (closure_minimal (t := {ζ : ℂ | z.im / (4 * R + 2) ≤ ζ.im}) ?_
    (isClosed_le continuous_const Complex.continuous_im)).trans fun ζ hζ => lt_of_lt_of_le hz hζ
  intro ζ hζ
  by_contra h
  exact hζ (radialTest_eq_zero_of_im_lt hR hφR z (not_le.1 h))

include hR hφR in
theorem realLaplacian_radialTest_of_im_nonpos (z : ℍ) {ζ : ℂ} (hζ : ζ.im ≤ 0) :
    realLaplacian (radialTest φ z) ζ = 0 := by
  have hz : 0 < z.im / (4 * R + 2) := div_pos z.im_pos (by linarith)
  have hopen : IsOpen {ζ : ℂ | ζ.im < z.im / (4 * R + 2)} :=
    isOpen_lt Complex.continuous_im continuous_const
  have h0 : ∀ ζ' ∈ {ζ : ℂ | ζ.im < z.im / (4 * R + 2)}, radialTest φ z =ᶠ[𝓝 ζ'] fun _ => 0 :=
    fun ζ' hζ' => by
      filter_upwards [hopen.mem_nhds hζ'] with ζ'' hζ''
      exact radialTest_eq_zero_of_im_lt hR hφR z hζ''
  have hdir : ∀ v, dir v (radialTest φ z) =ᶠ[𝓝 ζ] fun _ => 0 := fun v => by
    filter_upwards [hopen.mem_nhds (show ζ.im < z.im / (4 * R + 2) by linarith)] with ζ' hζ'
    unfold dir
    rw [(h0 ζ' hζ').fderiv_eq]
    simp
  unfold realLaplacian
  change fderiv ℝ (dir 1 (radialTest φ z)) ζ 1 +
    fderiv ℝ (dir Complex.I (radialTest φ z)) ζ Complex.I = 0
  rw [(hdir 1).fderiv_eq, (hdir Complex.I).fderiv_eq]
  simp

include hφ hφR in
theorem realLaplacian_radialTest (z : ℍ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    realLaplacian (radialTest φ z) ζ = radialLap φ (pairUc ζ z) / ζ.im ^ 2 := by
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hK := radial_kernelC1 hφ hφR
  have hK2 := radial_kernelC1_deriv hφ hφR
  have heq : ∀ ζ' ∈ {ζ : ℂ | 0 < ζ.im}, radialTest φ z =ᶠ[𝓝 ζ'] fun ζ => radialK φ ζ z :=
    fun ζ' hζ' => by
      filter_upwards [hopen.mem_nhds hζ'] with ζ'' hζ''
      exact radialTest_of_im_pos φ z hζ''
  have hdir : ∀ v, dir v (radialTest φ z) =ᶠ[𝓝 ζ] fun ζ' => radialK' φ ζ' z v := fun v => by
    filter_upwards [hopen.mem_nhds hζ] with ζ' hζ'
    unfold dir
    rw [(heq ζ' hζ').fderiv_eq, (hK.hasFDerivAt ζ' hζ' z).fderiv]
  have h1 : ∀ v, dir v (dir v (radialTest φ z)) ζ = radialK'' φ v ζ z v := fun v => by
    change fderiv ℝ (dir v (radialTest φ z)) ζ v = _
    rw [(hdir v).fderiv_eq, ((hK2 v).hasFDerivAt ζ hζ z).fderiv]
  unfold realLaplacian
  rw [h1, h1, radialK''_trace hζ z]

end Test

/-! ## The Green identity against radial kernels -/

/-- Two chart directional derivatives commute with a continuous real-linear map. -/
theorem dir_dir_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {V : ℂ → E}
    (hV : ContDiffOn ℝ 2 V {ζ : ℂ | 0 < ζ.im}) (g : E →L[ℝ] F) {ζ : ℂ} (hζ : 0 < ζ.im) (v : ℂ) :
    dir v (dir v (fun ζ => g (V ζ))) ζ = g (dir v (dir v V) ζ) := by
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd1 : ContDiffOn ℝ 1 (dir v V) {ζ : ℂ | 0 < ζ.im} := dir_contDiffOn hV (by norm_num) v
  have hdir : dir v (fun ζ => g (V ζ)) =ᶠ[𝓝 ζ] fun ζ' => g (dir v V ζ') := by
    filter_upwards [hopen.mem_nhds hζ] with ζ' hζ'
    have hdiff : DifferentiableAt ℝ V ζ' :=
      (hV.contDiffAt (hopen.mem_nhds hζ')).differentiableAt (by norm_num)
    unfold dir
    rw [fderiv_fun_comp ζ' g.differentiableAt hdiff, g.fderiv]
    rfl
  change fderiv ℝ (dir v (fun ζ => g (V ζ))) ζ v = _
  rw [hdir.fderiv_eq]
  have hdiff : DifferentiableAt ℝ (dir v V) ζ :=
    (hd1.contDiffAt (hopen.mem_nhds hζ)).differentiableAt (by norm_num)
  rw [fderiv_fun_comp ζ g.differentiableAt hdiff, g.fderiv]
  rfl

/-- The chart Laplacian `∂ₓ² + ∂ᵧ²` of `V ∘ ofComplex` at a point of `ℍ`. -/
def chartLap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : ℍ → E) (w : ℍ) : E :=
  dir 1 (dir 1 (fun ζ => V (ofComplex ζ))) w + dir Complex.I (dir Complex.I (fun ζ => V (ofComplex ζ))) w

theorem continuous_chartLap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : ℍ → E}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) : Continuous (chartLap V) := by
  have h : ∀ v, ContinuousOn (dir v (dir v (fun ζ => V (ofComplex ζ)))) {ζ : ℂ | 0 < ζ.im} :=
    fun v => (dir_contDiffOn (dir_contDiffOn hV (m := 1) (by norm_num) v) (m := 0) (by norm_num)
      v).continuousOn
  exact ((h 1).comp_continuous continuous_coe fun w => w.im_pos).add
    ((h Complex.I).comp_continuous continuous_coe fun w => w.im_pos)

section Green

variable {φ : ℝ → ℝ} {R : ℝ} (hφ : ContDiff ℝ 2 φ) (hR : 0 ≤ R) (hφR : KernelSupport φ R)

include hφ hφR in
theorem integrable_radial_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℍ → E} (hG : Continuous G) (z : ℍ) : Integrable (fun w => φ (pairU z w) • G w) := by
  have h := (radial_kernelC1 hφ hφR).integrable_smul hG z.im_pos
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [radialK]
  rw [pairUc_ofComplex z.im_pos, ofComplex_apply]

include hφ hR hφR in
/-- **Green identity on `ℍ`**: `∫ φ(u(z,w)) y² ΔV(w) dμ(w) = ∫ Dφ(u(z,w)) V(w) dμ(w)` for
`V ∈ C²`, where `y²Δ` is the Laplace–Beltrami operator. -/
theorem integral_radial_smul_chartLap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {V : ℍ → E} (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (z : ℍ) :
    ∫ w : ℍ, φ (pairU z w) • ((w.im ^ 2) • chartLap V w) =
      ∫ w : ℍ, radialLap φ (pairU z w) • V w := by
  have hVc : Continuous V := by
    have h := hV.continuousOn.comp_continuous continuous_coe fun w => w.im_pos
    simpa [Function.comp_def, ofComplex_apply] using h
  have hlapφ : ContDiff ℝ 0 (radialLap φ) := by
    unfold radialLap
    have h1 := (contDiff_one_deriv hφ).continuous
    have h2 := continuous_deriv_deriv hφ
    exact contDiff_zero.2 (by fun_prop)
  have hlapR : KernelSupport (radialLap φ) R := fun u hu => by
    simp [radialLap, deriv_eq_zero_of_kernelSupport hφR hu,
      deriv_eq_zero_of_kernelSupport (kernelSupport_deriv hφR) hu]
  have iL : Integrable (fun w : ℍ => φ (pairU z w) • ((w.im ^ 2) • chartLap V w)) :=
    integrable_radial_smul hφ hφR
      ((UpperHalfPlane.continuous_im.pow 2).smul (continuous_chartLap hV)) z
  have iR : Integrable (fun w => radialLap φ (pairU z w) • V w) := by
    have hc : Continuous (fun w => radialLap φ (pairU z w) • V w) :=
      ((contDiff_zero.1 hlapφ).comp (continuous_pairU_right z)).smul hVc
    refine (integrableOn_iff_integrable_of_support_subset
      (s := Metric.closedBall z (1 + 2 * R)) ?_).1
      (hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    intro w hw
    by_contra hwK
    apply hw
    have : R < pairU z w := by
      by_contra h
      push Not at h
      exact hwK (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
    simp [hlapR _ this]
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g => ?_
  rw [← ContinuousLinearMap.integral_comp_comm g iL, ← ContinuousLinearMap.integral_comp_comm g iR,
    integral_eq_chart, integral_eq_chart]
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hgV : ContDiffOn ℝ 2 (fun ζ => g (V (ofComplex ζ))) {ζ : ℂ | 0 < ζ.im} :=
    g.contDiff.comp_contDiffOn hV
  have hL : ∀ ζ ∈ {ζ : ℂ | 0 < ζ.im}, ((ζ.im ^ 2)⁻¹ : ℝ) •
      g (φ (pairU z (ofComplex ζ)) • (((ofComplex ζ).im ^ 2) • chartLap V (ofComplex ζ))) =
        radialTest φ z ζ * realLaplacian (fun ζ => g (V (ofComplex ζ))) ζ := by
    intro ζ hζ
    have hζ' : 0 < ζ.im := hζ
    have him : (ofComplex ζ).im = ζ.im := by rw [ofComplex_apply_of_im_pos hζ']; rfl
    have hcoe : ((ofComplex ζ : ℍ) : ℂ) = ζ := by rw [ofComplex_apply_of_im_pos hζ']
    rw [map_smul, map_smul, him, radialTest_of_im_pos φ z hζ', pairU_comm, ← pairUc_ofComplex hζ']
    unfold chartLap realLaplacian
    rw [hcoe, map_add, dir_dir_comp_clm hV g hζ', dir_dir_comp_clm hV g hζ', smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    field_simp
  have hR' : ∀ ζ ∈ {ζ : ℂ | 0 < ζ.im}, ((ζ.im ^ 2)⁻¹ : ℝ) •
      g (radialLap φ (pairU z (ofComplex ζ)) • V (ofComplex ζ)) =
        realLaplacian (radialTest φ z) ζ * g (V (ofComplex ζ)) := by
    intro ζ hζ
    have hζ' : 0 < ζ.im := hζ
    rw [map_smul, realLaplacian_radialTest hφ hφR z hζ', pairU_comm, ← pairUc_ofComplex hζ',
      smul_eq_mul, smul_eq_mul]
    field_simp
  rw [setIntegral_congr_fun hopen.measurableSet hL, setIntegral_congr_fun hopen.measurableSet hR']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => by
      rw [show radialTest φ z ζ = 0 by
        unfold radialTest; exact if_neg hζ]; simp,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => by
      rw [realLaplacian_radialTest_of_im_nonpos hR hφR z (not_lt.1 hζ), zero_mul]]
  exact integral_test_laplacian (contDiff_radialTest hφ hR hφR z)
    (hasCompactSupport_radialTest hR hφR z) (tsupport_radialTest_subset hR hφR z) hgV

end Green

end

end GaloisForLFunctions.RHTower.DeckPointPair
