import GaloisForLFunctions.RHTower.DeckPointPairCuspidal
import GaloisForLFunctions.RHTower.SelbergLocalTestGreen

/-!
# Kernel integrals over the upper half-plane and the Laplacian of radial kernels

For a kernel `K(ζ, w)` which is `C¹` in the chart variable `ζ` on the upper half-plane, jointly
continuous with its derivative, and supported in `U(ζ, w) ≤ R`, the kernel integral
`ζ ↦ ∫_ℍ K(ζ, w) G(w) dμ(w)` of a continuous `G` is `C¹` and may be differentiated under the
integral sign; the uniform bounds come from continuity on a compact set because the support stays
in a fixed hyperbolic ball.  If every directional derivative kernel is again `C¹`, the integral is
`C²`.

For the radial kernel `φ(U(ζ, w))` with `φ ∈ C²` the second derivatives are
`φ''(U) (∂U)² + φ'(U) ∂²U`, and the identities `(Im ζ)² |∇U|² = U(U+1)` and
`(Im ζ)² ΔU = 2U + 1` give
`(∂ₓ² + ∂ᵧ²) ∫ φ(U(ζ, w)) G(w) dμ(w) = (Im ζ)⁻² ∫ Dφ(U(ζ, w)) G(w) dμ(w)`
with `Dφ(u) = u(u+1)φ''(u) + (2u+1)φ'(u)`.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.DeckPointPair

open GaloisForLFunctions.HTGeometry SelbergMaassTraceEnergy

noncomputable section

/-! ## Geometry of the kernel support -/

theorem im_pos_of_norm_sub_lt {ζ₀ ζ : ℂ} (hζ : ‖ζ - ζ₀‖ < ζ₀.im / 2) :
    ζ₀.im / 2 < ζ.im := by
  have h1 := Complex.abs_im_le_norm (ζ - ζ₀)
  rw [Complex.sub_im] at h1
  have := abs_lt.1 (h1.trans_lt hζ)
  linarith

/-- Near `ζ₀` the support `U(ζ, w) ≤ R` stays in a fixed hyperbolic ball about `ζ₀`. -/
theorem mem_closedBall_of_pairUc_le {ζ₀ ζ : ℂ} (hζ₀ : 0 < ζ₀.im) (hζ : ‖ζ - ζ₀‖ < ζ₀.im / 2)
    {w : ℍ} {R : ℝ} (h : pairUc ζ w ≤ R) :
    w ∈ Metric.closedBall (ofComplex ζ₀) (2 + 2 * R) := by
  have hζp : 0 < ζ.im := by linarith [im_pos_of_norm_sub_lt hζ]
  rw [pairUc_ofComplex hζp] at h
  have h1 := dist_le_of_pairU_le h
  have h2 := dist_ofComplex_le_one hζ₀ hζ
  rw [Metric.mem_closedBall]
  linarith [dist_triangle w (ofComplex ζ) (ofComplex ζ₀), dist_comm w (ofComplex ζ),
    dist_comm (ofComplex ζ) (ofComplex ζ₀)]

/-! ## Kernel integrals in the chart variable -/

section KernelIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The kernel integral `∫_ℍ K(ζ, w) G(w) dμ(w)` as a function of the chart variable `ζ`. -/
def kerInt (K : ℂ → ℍ → ℝ) (G : ℍ → E) (ζ : ℂ) : E := ∫ w : ℍ, K ζ w • G w

/-- The kernel integral of a derivative kernel. -/
def kerIntDeriv (K' : ℂ → ℍ → (ℂ →L[ℝ] ℝ)) (G : ℍ → E) (ζ : ℂ) : ℂ →L[ℝ] E :=
  ∫ w : ℍ, (K' ζ w).smulRight (G w)

/-- A kernel which is `C¹` in the chart variable on the upper half-plane and vanishes (with its
derivative) where `U(ζ, w) > R`. -/
structure KernelC1 (K : ℂ → ℍ → ℝ) (K' : ℂ → ℍ → (ℂ →L[ℝ] ℝ)) (R : ℝ) : Prop where
  hasFDerivAt : ∀ ζ : ℂ, 0 < ζ.im → ∀ w : ℍ, HasFDerivAt (fun ζ => K ζ w) (K' ζ w) ζ
  continuousOn : ContinuousOn (fun p : ℂ × ℍ => K p.1 p.2) ({ζ : ℂ | 0 < ζ.im} ×ˢ univ)
  continuousOn_deriv :
    ContinuousOn (fun p : ℂ × ℍ => K' p.1 p.2) ({ζ : ℂ | 0 < ζ.im} ×ˢ univ)
  support : ∀ ζ : ℂ, 0 < ζ.im → ∀ w : ℍ, R < pairUc ζ w → K ζ w = 0 ∧ K' ζ w = 0

namespace KernelC1

variable {K : ℂ → ℍ → ℝ} {K' : ℂ → ℍ → (ℂ →L[ℝ] ℝ)} {R : ℝ}

theorem continuous_right (hK : KernelC1 K K' R) {ζ : ℂ} (hζ : 0 < ζ.im) :
    Continuous (fun w => K ζ w) :=
  hK.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hζ, trivial⟩

theorem continuous_deriv_right (hK : KernelC1 K K' R) {ζ : ℂ} (hζ : 0 < ζ.im) :
    Continuous (fun w => K' ζ w) :=
  hK.continuousOn_deriv.comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨hζ, trivial⟩

theorem eq_zero_of_not_mem (hK : KernelC1 K K' R) {ζ₀ ζ : ℂ} (hζ₀ : 0 < ζ₀.im)
    (hζ : ‖ζ - ζ₀‖ < ζ₀.im / 2) {w : ℍ} (hw : w ∉ Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)) :
    K ζ w = 0 ∧ K' ζ w = 0 := by
  have hζp : 0 < ζ.im := by linarith [im_pos_of_norm_sub_lt hζ]
  refine hK.support ζ hζp w ?_
  by_contra h
  exact hw (mem_closedBall_of_pairUc_le hζ₀ hζ (not_lt.1 h))

/-- Uniform bounds near `ζ₀`, from continuity on a compact set and the support condition. -/
theorem exists_bound (hK : KernelC1 K K' R) {ζ₀ : ℂ} (hζ₀ : 0 < ζ₀.im) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ ζ ∈ Metric.closedBall ζ₀ (ζ₀.im / 4), ∀ w : ℍ,
      |K ζ w| ≤ C₀ ∧ ‖K' ζ w‖ ≤ C₁ := by
  have hS : IsCompact (Metric.closedBall ζ₀ (ζ₀.im / 4) ×ˢ
      Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hsub : Metric.closedBall ζ₀ (ζ₀.im / 4) ×ˢ Metric.closedBall (ofComplex ζ₀) (2 + 2 * R) ⊆
      {ζ : ℂ | 0 < ζ.im} ×ˢ univ := by
    rintro ⟨ζ, w⟩ ⟨hζ, -⟩
    refine ⟨?_, trivial⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    have := im_pos_of_norm_sub_lt (hζ.trans_lt (by linarith))
    show 0 < ζ.im
    linarith
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn (hK.continuousOn.mono hsub)
  obtain ⟨C₁, hC₁⟩ := hS.exists_bound_of_continuousOn (hK.continuousOn_deriv.mono hsub)
  refine ⟨max C₀ 0, max C₁ 0, le_max_right _ _, le_max_right _ _, fun ζ hζ w => ?_⟩
  by_cases hw : w ∈ Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)
  · exact ⟨(hC₀ (ζ, w) ⟨hζ, hw⟩).trans (le_max_left _ _),
      (hC₁ (ζ, w) ⟨hζ, hw⟩).trans (le_max_left _ _)⟩
  · rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    obtain ⟨h0, h1⟩ := hK.eq_zero_of_not_mem hζ₀ (hζ.trans_lt (by linarith)) hw
    rw [h0, h1]
    simp

omit [NormedSpace ℝ E] in
theorem integrable_bound {G : ℍ → E} (hG : Continuous G) (z : ℍ) (C r : ℝ) :
    Integrable ((Metric.closedBall z r).indicator fun w => C * ‖G w‖) := by
  rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  exact (continuous_const.mul hG.norm).continuousOn.integrableOn_compact (isCompact_closedBall _ _)

theorem integrable_smul (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) {ζ : ℂ}
    (hζ : 0 < ζ.im) : Integrable (fun w => K ζ w • G w) := by
  obtain ⟨C₀, C₁, hC₀, -, hC⟩ := hK.exists_bound hζ
  refine (integrable_bound hG (ofComplex ζ) C₀ (2 + 2 * R)).mono'
    ((hK.continuous_right hζ).smul hG).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  have hself : ζ ∈ Metric.closedBall ζ (ζ.im / 4) := Metric.mem_closedBall_self (by linarith)
  by_cases hw : w ∈ Metric.closedBall (ofComplex ζ) (2 + 2 * R)
  · rw [indicator_of_mem hw, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC ζ hself w).1 (norm_nonneg _)
  · rw [indicator_of_notMem hw, (hK.eq_zero_of_not_mem hζ (by simp; linarith) hw).1, zero_smul,
      norm_zero]

theorem integrable_smulRight (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) {ζ : ℂ}
    (hζ : 0 < ζ.im) : Integrable (fun w => (K' ζ w).smulRight (G w)) := by
  obtain ⟨C₀, C₁, -, hC₁, hC⟩ := hK.exists_bound hζ
  have hmeas : Continuous (fun w => (K' ζ w).smulRight (G w)) :=
    (ContinuousLinearMap.smulRightL ℝ ℂ E).continuous₂.comp
      ((hK.continuous_deriv_right hζ).prodMk hG)
  refine (integrable_bound hG (ofComplex ζ) C₁ (2 + 2 * R)).mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  have hself : ζ ∈ Metric.closedBall ζ (ζ.im / 4) := Metric.mem_closedBall_self (by linarith)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  by_cases hw : w ∈ Metric.closedBall (ofComplex ζ) (2 + 2 * R)
  · rw [indicator_of_mem hw]
    exact mul_le_mul_of_nonneg_right (hC ζ hself w).2 (norm_nonneg _)
  · rw [indicator_of_notMem hw, (hK.eq_zero_of_not_mem hζ (by simp; linarith) hw).2, norm_zero,
      zero_mul]

/-- **Differentiation under the integral sign.** -/
theorem hasFDerivAt_kerInt (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) {ζ₀ : ℂ}
    (hζ₀ : 0 < ζ₀.im) : HasFDerivAt (kerInt K G) (kerIntDeriv K' G ζ₀) ζ₀ := by
  obtain ⟨C₀, C₁, -, hC₁, hC⟩ := hK.exists_bound hζ₀
  have hε : 0 < ζ₀.im / 4 := by linarith
  have hsmall : ∀ ζ ∈ Metric.ball ζ₀ (ζ₀.im / 4), ‖ζ - ζ₀‖ < ζ₀.im / 2 ∧ 0 < ζ.im := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    have h2 : ‖ζ - ζ₀‖ < ζ₀.im / 2 := hζ.trans (by linarith)
    exact ⟨h2, by linarith [im_pos_of_norm_sub_lt h2]⟩
  unfold kerInt kerIntDeriv
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun ζ w => K ζ w • G w) (F' := fun ζ w => (K' ζ w).smulRight (G w))
    (bound := (Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)).indicator fun w => C₁ * ‖G w‖)
    (Metric.ball_mem_nhds ζ₀ hε) ?_ (hK.integrable_smul hG hζ₀)
    (hK.integrable_smulRight hG hζ₀).aestronglyMeasurable ?_
    (integrable_bound hG _ _ _) ?_
  · filter_upwards [Metric.ball_mem_nhds ζ₀ hε] with ζ hζ
    exact ((hK.continuous_right (hsmall ζ hζ).2).smul hG).aestronglyMeasurable
  · refine Eventually.of_forall fun w ζ hζ => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply]
    by_cases hw : w ∈ Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)
    · rw [indicator_of_mem hw]
      exact mul_le_mul_of_nonneg_right (hC ζ (Metric.ball_subset_closedBall hζ) w).2
        (norm_nonneg _)
    · rw [indicator_of_notMem hw, (hK.eq_zero_of_not_mem hζ₀ (hsmall ζ hζ).1 hw).2, norm_zero,
        zero_mul]
  · exact Eventually.of_forall fun w ζ hζ =>
      (hK.hasFDerivAt ζ (hsmall ζ hζ).2 w).smul_const (G w)

/-- **Continuity of the differentiated kernel integral.** -/
theorem continuousOn_kerIntDeriv (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) :
    ContinuousOn (kerIntDeriv K' G) {ζ : ℂ | 0 < ζ.im} := by
  intro ζ₀ hζ₀
  have hζ₀' : 0 < ζ₀.im := hζ₀
  obtain ⟨C₀, C₁, -, hC₁, hC⟩ := hK.exists_bound hζ₀'
  have hε : 0 < ζ₀.im / 4 := by linarith
  have hsmall : ∀ ζ ∈ Metric.ball ζ₀ (ζ₀.im / 4), ‖ζ - ζ₀‖ < ζ₀.im / 2 ∧ 0 < ζ.im := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    have h2 : ‖ζ - ζ₀‖ < ζ₀.im / 2 := hζ.trans (by linarith)
    exact ⟨h2, by linarith [im_pos_of_norm_sub_lt h2]⟩
  refine ContinuousAt.continuousWithinAt ?_
  unfold kerIntDeriv
  refine continuousAt_of_dominated
    (bound := (Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)).indicator fun w => C₁ * ‖G w‖)
    ?_ ?_ (integrable_bound hG _ _ _) ?_
  · filter_upwards [Metric.ball_mem_nhds ζ₀ hε] with ζ hζ
    exact (hK.integrable_smulRight hG (hsmall ζ hζ).2).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds ζ₀ hε] with ζ hζ
    refine Eventually.of_forall fun w => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply]
    by_cases hw : w ∈ Metric.closedBall (ofComplex ζ₀) (2 + 2 * R)
    · rw [indicator_of_mem hw]
      exact mul_le_mul_of_nonneg_right (hC ζ (Metric.ball_subset_closedBall hζ) w).2
        (norm_nonneg _)
    · rw [indicator_of_notMem hw, (hK.eq_zero_of_not_mem hζ₀' (hsmall ζ hζ).1 hw).2, norm_zero,
        zero_mul]
  · refine Eventually.of_forall fun w => ?_
    have hopen : IsOpen ({ζ : ℂ | 0 < ζ.im} ×ˢ (univ : Set ℍ)) :=
      (isOpen_lt continuous_const Complex.continuous_im).prod isOpen_univ
    have hc : ContinuousAt (fun p : ℂ × ℍ => K' p.1 p.2) (ζ₀, w) :=
      hK.continuousOn_deriv.continuousAt (hopen.mem_nhds ⟨hζ₀', trivial⟩)
    have hL : Continuous (fun c : ℂ →L[ℝ] ℝ => c.smulRight (G w)) :=
      ((ContinuousLinearMap.smulRightL ℝ ℂ E).flip (G w)).continuous
    have hc' : ContinuousAt (fun x : ℂ => K' x w) ζ₀ :=
      hc.comp (f := fun x : ℂ => (x, w)) (continuousAt_id.prodMk continuousAt_const)
    exact hL.continuousAt.comp hc'

theorem fderiv_kerInt (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) {ζ : ℂ}
    (hζ : 0 < ζ.im) : fderiv ℝ (kerInt K G) ζ = kerIntDeriv K' G ζ :=
  (hK.hasFDerivAt_kerInt hG hζ).fderiv

/-- **`C¹` regularity of kernel integrals.** -/
theorem contDiffOn_kerInt (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) :
    ContDiffOn ℝ 1 (kerInt K G) {ζ : ℂ | 0 < ζ.im} := by
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hopen]
  refine ⟨fun ζ hζ => (hK.hasFDerivAt_kerInt hG hζ).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (hK.continuousOn_kerIntDeriv hG).congr fun ζ hζ => hK.fderiv_kerInt hG hζ

theorem kerIntDeriv_apply (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) {ζ : ℂ}
    (hζ : 0 < ζ.im) (v : ℂ) :
    kerIntDeriv K' G ζ v = kerInt (fun ζ w => K' ζ w v) G ζ := by
  unfold kerIntDeriv kerInt
  rw [ContinuousLinearMap.integral_apply (hK.integrable_smulRight hG hζ)]
  rfl

/-- The directional derivative of a kernel integral is the kernel integral of the directional
derivative kernel. -/
theorem dir_kerInt_eventuallyEq (hK : KernelC1 K K' R) {G : ℍ → E} (hG : Continuous G) {ζ : ℂ}
    (hζ : 0 < ζ.im) (v : ℂ) :
    dir v (kerInt K G) =ᶠ[𝓝 ζ] kerInt (fun ζ w => K' ζ w v) G := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ] with ζ' hζ'
  unfold dir
  rw [hK.fderiv_kerInt hG hζ', hK.kerIntDeriv_apply hG hζ']

/-- **`C²` regularity of kernel integrals** when every directional derivative kernel is `C¹`. -/
theorem contDiffOn_two_kerInt (hK : KernelC1 K K' R) {K'' : ℂ → ℂ → ℍ → (ℂ →L[ℝ] ℝ)}
    (hK2 : ∀ v, KernelC1 (fun ζ w => K' ζ w v) (K'' v) R) {G : ℍ → E} (hG : Continuous G) :
    ContDiffOn ℝ 2 (kerInt K G) {ζ : ℂ | 0 < ζ.im} := by
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hopen]
  refine ⟨fun ζ hζ => (hK.hasFDerivAt_kerInt hG hζ).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_clm_apply]
  intro v
  exact ((hK2 v).contDiffOn_kerInt hG).congr fun ζ hζ => by
    rw [hK.fderiv_kerInt hG hζ, hK.kerIntDeriv_apply hG hζ]

/-- Second directional derivatives of a kernel integral. -/
theorem dir_dir_kerInt (hK : KernelC1 K K' R) {K'' : ℂ → ℂ → ℍ → (ℂ →L[ℝ] ℝ)}
    (hK2 : ∀ v, KernelC1 (fun ζ w => K' ζ w v) (K'' v) R) {G : ℍ → E} (hG : Continuous G)
    {ζ : ℂ} (hζ : 0 < ζ.im) (v : ℂ) :
    dir v (dir v (kerInt K G)) ζ = kerInt (fun ζ w => K'' v ζ w v) G ζ := by
  change fderiv ℝ (dir v (kerInt K G)) ζ v = _
  rw [(hK.dir_kerInt_eventuallyEq hG hζ v).fderiv_eq, (hK2 v).fderiv_kerInt hG hζ,
    (hK2 v).kerIntDeriv_apply hG hζ]

end KernelC1

end KernelIntegral

/-! ## Radial kernels -/

/-- Second chart derivatives of `U`: the derivative of `ζ ↦ dU(ζ, w) v`. -/
def pairUcHess (ζ : ℂ) (w : ℍ) (v : ℂ) : ℂ →L[ℝ] ℝ :=
  (v.re * (1 / (2 * ζ.im * w.im)) - v.im * ((ζ.re - w.re) / (2 * ζ.im ^ 2 * w.im))) •
      Complex.reCLM +
    (-(v.re * ((ζ.re - w.re) / (2 * ζ.im ^ 2 * w.im))) +
      v.im * ((w.im ^ 2 + (ζ.re - w.re) ^ 2) / (2 * ζ.im ^ 3 * w.im))) • Complex.imCLM

theorem pairUcDeriv_apply (ζ : ℂ) (w : ℍ) (v : ℂ) :
    pairUcDeriv ζ w v = (ζ.re - w.re) / (2 * ζ.im * w.im) * v.re +
      (ζ.im ^ 2 - w.im ^ 2 - (ζ.re - w.re) ^ 2) / (4 * ζ.im ^ 2 * w.im) * v.im := by
  simp [pairUcDeriv]

theorem hasFDerivAt_pairUcDeriv_apply {ζ : ℂ} (hζ : 0 < ζ.im) (w : ℍ) (v : ℂ) :
    HasFDerivAt (fun ζ => pairUcDeriv ζ w v) (pairUcHess ζ w v) ζ := by
  have hw := w.im_pos
  have hre : HasFDerivAt (fun ζ : ℂ => ζ.re - w.re) Complex.reCLM ζ :=
    (Complex.reCLM.hasFDerivAt).sub_const _
  have him : HasFDerivAt (fun ζ : ℂ => ζ.im) Complex.imCLM ζ := Complex.imCLM.hasFDerivAt
  have hinv : HasFDerivAt (fun ζ : ℂ => (ζ.im)⁻¹) ((-(ζ.im ^ 2)⁻¹) • Complex.imCLM) ζ :=
    (hasDerivAt_inv hζ.ne').comp_hasFDerivAt ζ Complex.imCLM.hasFDerivAt
  have ha := (hre.mul hinv).mul_const ((2 * w.im)⁻¹ * v.re)
  have hb := ((((him.mul him).sub_const (w.im ^ 2)).sub (hre.mul hre)).mul hinv).mul hinv
  have h := ha.add (hb.mul_const ((4 * w.im)⁻¹ * v.im))
  have e : (fun ζ => pairUcDeriv ζ w v) = fun ζ : ℂ =>
      (ζ.re - w.re) * (ζ.im)⁻¹ * ((2 * w.im)⁻¹ * v.re) +
        ((ζ.im * ζ.im - w.im ^ 2 - (ζ.re - w.re) * (ζ.re - w.re)) * (ζ.im)⁻¹ * (ζ.im)⁻¹) *
          ((4 * w.im)⁻¹ * v.im) := by
    funext ζ
    rw [pairUcDeriv_apply]
    by_cases h0 : ζ.im = 0
    · simp [h0]
    · field_simp
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  simp only [pairUcHess, add_apply, smul_apply, sub_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

/-- `|∇U|²` identity: `(Im ζ)² ((∂ₓU)² + (∂ᵧU)²) = U (U + 1)`. -/
theorem pairUcDeriv_sq_add {ζ : ℂ} (hζ : 0 < ζ.im) (w : ℍ) :
    pairUcDeriv ζ w 1 ^ 2 + pairUcDeriv ζ w Complex.I ^ 2 =
      pairUc ζ w * (pairUc ζ w + 1) / ζ.im ^ 2 := by
  have hw := w.im_pos
  rw [pairUcDeriv_apply, pairUcDeriv_apply]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, pairUc]
  field_simp
  ring

/-- Laplacian identity: `(Im ζ)² (∂ₓ²U + ∂ᵧ²U) = 2U + 1`. -/
theorem pairUcHess_trace {ζ : ℂ} (hζ : 0 < ζ.im) (w : ℍ) :
    pairUcHess ζ w 1 1 + pairUcHess ζ w Complex.I Complex.I = (2 * pairUc ζ w + 1) / ζ.im ^ 2 := by
  have hw := w.im_pos
  simp only [pairUcHess, add_apply, smul_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, pairUc]
  field_simp
  ring

theorem continuousOn_pairUc_joint :
    ContinuousOn (fun p : ℂ × ℍ => pairUc p.1 p.2) ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) := by
  unfold pairUc
  have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
  have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_
  have h1 : 0 < p.1.im := hp.1
  have h2 := p.2.im_pos
  positivity

theorem continuousOn_pairUcDeriv_joint :
    ContinuousOn (fun p : ℂ × ℍ => pairUcDeriv p.1 p.2) ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) := by
  have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
  have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
  have ha : ContinuousOn (fun p : ℂ × ℍ => (p.1.re - p.2.re) / (2 * p.1.im * p.2.im))
      ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_
    have h1 : 0 < p.1.im := hp.1
    have h2 := p.2.im_pos
    positivity
  have hb : ContinuousOn (fun p : ℂ × ℍ =>
      (p.1.im ^ 2 - p.2.im ^ 2 - (p.1.re - p.2.re) ^ 2) / (4 * p.1.im ^ 2 * p.2.im))
      ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_
    have h1 : 0 < p.1.im := hp.1
    have h2 := p.2.im_pos
    positivity
  exact (ha.smul continuousOn_const).add (hb.smul continuousOn_const)

theorem continuousOn_pairUcHess_joint (v : ℂ) :
    ContinuousOn (fun p : ℂ × ℍ => pairUcHess p.1 p.2 v) ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) := by
  have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
  have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
  have hpos : ∀ p ∈ ({ζ : ℂ | 0 < ζ.im} ×ˢ (univ : Set ℍ)), 0 < p.1.im ∧ 0 < p.2.im :=
    fun p hp => ⟨hp.1, p.2.im_pos⟩
  have hc1 : ContinuousOn (fun p : ℂ × ℍ => (p.1.re - p.2.re) / (2 * p.1.im ^ 2 * p.2.im))
      ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => by
      obtain ⟨a, b⟩ := hpos p hp; positivity
  have hc2 : ContinuousOn (fun p : ℂ × ℍ => 1 / (2 * p.1.im * p.2.im))
      ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => by
      obtain ⟨a, b⟩ := hpos p hp; positivity
  have hc3 : ContinuousOn (fun p : ℂ × ℍ =>
      (p.2.im ^ 2 + (p.1.re - p.2.re) ^ 2) / (2 * p.1.im ^ 3 * p.2.im))
      ({ζ : ℂ | 0 < ζ.im} ×ˢ univ) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => by
      obtain ⟨a, b⟩ := hpos p hp; positivity
  have h1 := (continuousOn_const (c := v.re).mul hc2).sub (continuousOn_const (c := v.im).mul hc1)
  have h2 := (continuousOn_const (c := v.re).mul hc1).neg.add (continuousOn_const (c := v.im).mul hc3)
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

/-- The radial kernel `φ(U(ζ, w))`. -/
def radialK (φ : ℝ → ℝ) (ζ : ℂ) (w : ℍ) : ℝ := φ (pairUc ζ w)

/-- Its chart derivative `φ'(U) dU`. -/
def radialK' (φ : ℝ → ℝ) (ζ : ℂ) (w : ℍ) : ℂ →L[ℝ] ℝ := deriv φ (pairUc ζ w) • pairUcDeriv ζ w

/-- The derivative of `ζ ↦ φ'(U) dU(v)`. -/
def radialK'' (φ : ℝ → ℝ) (v : ℂ) (ζ : ℂ) (w : ℍ) : ℂ →L[ℝ] ℝ :=
  (deriv (deriv φ) (pairUc ζ w) * pairUcDeriv ζ w v) • pairUcDeriv ζ w +
    deriv φ (pairUc ζ w) • pairUcHess ζ w v

/-- The radial Laplacian `Dφ(u) = u(u+1)φ''(u) + (2u+1)φ'(u)`. -/
def radialLap (φ : ℝ → ℝ) (u : ℝ) : ℝ := u * (u + 1) * deriv (deriv φ) u + (2 * u + 1) * deriv φ u

section Radial

variable {φ : ℝ → ℝ} {R : ℝ} (hφ : ContDiff ℝ 2 φ) (hφR : KernelSupport φ R)
include hφ

theorem differentiable_of_contDiff_two : Differentiable ℝ φ :=
  hφ.differentiable (by norm_num)

theorem contDiff_one_deriv : ContDiff ℝ 1 (deriv φ) :=
  (contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) φ from hφ)).2.2

theorem differentiable_deriv_of_contDiff_two : Differentiable ℝ (deriv φ) :=
  (contDiff_one_deriv hφ).differentiable (by norm_num)

theorem continuous_deriv_deriv : Continuous (deriv (deriv φ)) :=
  (contDiff_one_iff_deriv.1 (contDiff_one_deriv hφ)).2

include hφR

omit hφ in
theorem kernelSupport_deriv : KernelSupport (deriv φ) R := fun _ hu =>
  deriv_eq_zero_of_kernelSupport hφR hu

theorem radial_kernelC1 : KernelC1 (radialK φ) (radialK' φ) R where
  hasFDerivAt ζ hζ w :=
    ((differentiable_of_contDiff_two hφ _).hasDerivAt.comp_hasFDerivAt ζ
      (hasFDerivAt_pairUc hζ w))
  continuousOn := (differentiable_of_contDiff_two hφ).continuous.comp_continuousOn
    continuousOn_pairUc_joint
  continuousOn_deriv := ((contDiff_one_deriv hφ).continuous.comp_continuousOn
    continuousOn_pairUc_joint).smul continuousOn_pairUcDeriv_joint
  support ζ _ w h := by
    refine ⟨hφR _ h, ?_⟩
    simp [radialK', deriv_eq_zero_of_kernelSupport hφR h]

theorem radial_kernelC1_deriv (v : ℂ) :
    KernelC1 (fun ζ w => radialK' φ ζ w v) (radialK'' φ v) R where
  hasFDerivAt ζ hζ w := by
    have h1 : HasFDerivAt (fun ζ => deriv φ (pairUc ζ w))
        (deriv (deriv φ) (pairUc ζ w) • pairUcDeriv ζ w) ζ :=
      (differentiable_deriv_of_contDiff_two hφ _).hasDerivAt.comp_hasFDerivAt ζ
        (hasFDerivAt_pairUc hζ w)
    have h2 := hasFDerivAt_pairUcDeriv_apply hζ w v
    have h := h1.mul h2
    have e : (fun ζ => radialK' φ ζ w v) = fun ζ => deriv φ (pairUc ζ w) * pairUcDeriv ζ w v := by
      funext ζ; simp [radialK']
    rw [e]
    refine h.congr_fderiv ?_
    unfold radialK''
    rw [smul_smul, add_comm, mul_comm (pairUcDeriv ζ w v)]
  continuousOn := by
    have e : (fun p : ℂ × ℍ => radialK' φ p.1 p.2 v) =
        fun p => deriv φ (pairUc p.1 p.2) * pairUcDeriv p.1 p.2 v := by
      funext p; simp [radialK']
    rw [e]
    exact ((contDiff_one_deriv hφ).continuous.comp_continuousOn continuousOn_pairUc_joint).mul
      (continuousOn_pairUcDeriv_joint.clm_apply continuousOn_const)
  continuousOn_deriv := by
    unfold radialK''
    refine ((((continuous_deriv_deriv hφ).comp_continuousOn continuousOn_pairUc_joint).mul
      (continuousOn_pairUcDeriv_joint.clm_apply continuousOn_const)).smul
      continuousOn_pairUcDeriv_joint).add ?_
    exact ((contDiff_one_deriv hφ).continuous.comp_continuousOn continuousOn_pairUc_joint).smul
      (continuousOn_pairUcHess_joint v)
  support ζ _ w h := by
    have h1 := deriv_eq_zero_of_kernelSupport hφR h
    have h2 := deriv_eq_zero_of_kernelSupport (kernelSupport_deriv hφR) h
    refine ⟨by simp [radialK', h1], ?_⟩
    simp [radialK'', h1, h2]

omit hφ hφR in
theorem radialK''_trace {ζ : ℂ} (hζ : 0 < ζ.im) (w : ℍ) :
    radialK'' φ 1 ζ w 1 + radialK'' φ Complex.I ζ w Complex.I =
      radialLap φ (pairUc ζ w) / ζ.im ^ 2 := by
  have e : radialK'' φ 1 ζ w 1 + radialK'' φ Complex.I ζ w Complex.I =
      deriv (deriv φ) (pairUc ζ w) * (pairUcDeriv ζ w 1 ^ 2 + pairUcDeriv ζ w Complex.I ^ 2) +
        deriv φ (pairUc ζ w) * (pairUcHess ζ w 1 1 + pairUcHess ζ w Complex.I Complex.I) := by
    simp only [radialK'', add_apply, smul_apply, smul_eq_mul]
    ring
  rw [e, pairUcDeriv_sq_add hζ w, pairUcHess_trace hζ w]
  unfold radialLap
  ring

/-- **The Laplacian of a radial kernel integral** is the kernel integral of `Dφ`:
`(∂ₓ² + ∂ᵧ²) ∫ φ(U(ζ, w)) G(w) dμ(w) = (Im ζ)⁻² ∫ Dφ(U(ζ, w)) G(w) dμ(w)`. -/
theorem laplacian_kerInt_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℍ → E} (hG : Continuous G) {ζ : ℂ} (hζ : 0 < ζ.im) :
    dir 1 (dir 1 (kerInt (radialK φ) G)) ζ +
        dir Complex.I (dir Complex.I (kerInt (radialK φ) G)) ζ =
      (ζ.im ^ 2)⁻¹ • kerInt (radialK (radialLap φ)) G ζ := by
  have hK := radial_kernelC1 hφ hφR
  have hK2 := radial_kernelC1_deriv hφ hφR
  rw [hK.dir_dir_kerInt hK2 hG hζ, hK.dir_dir_kerInt hK2 hG hζ]
  have i1 : Integrable (fun w => radialK'' φ 1 ζ w 1 • G w) :=
    ((hK2 1).integrable_smulRight hG hζ).apply_continuousLinearMap 1
  have iI : Integrable (fun w => radialK'' φ Complex.I ζ w Complex.I • G w) :=
    ((hK2 Complex.I).integrable_smulRight hG hζ).apply_continuousLinearMap Complex.I
  unfold kerInt
  rw [← integral_add i1 iI, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [← add_smul, radialK''_trace hζ w, smul_smul, radialK]
  congr 1
  field_simp

end Radial

end

end GaloisForLFunctions.RHTower.DeckPointPair
