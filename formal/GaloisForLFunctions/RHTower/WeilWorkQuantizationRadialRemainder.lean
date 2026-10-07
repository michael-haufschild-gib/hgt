import GaloisForLFunctions.RHTower.WeilWorkQuantizationSubpolynomial
import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialTheta
import GaloisForLFunctions.RHTower.HamburgerAbelianTwistContour

/-!
# Refined radial remainder for the actual Weil source

Finite rectangle differences pass to the measurable radial trace and then to
a half-line. The arithmetic right edge supplies its resonant coefficient.
Every positive strip exponent up to one yields the refined radial error bound,
without any continuous critical-edge extension.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

def quantizationContourBound (C p : ℝ) (τ : ℂ) (y : ℝ) : ℝ :=
  C * (1 + |y|) ^ p * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
    Real.exp (-(|y| * (τ.re / ‖τ‖))))

/-- Keep the right edge in the difference, so that its resonant term can later be removed. -/
theorem norm_quantization_open_rectangle_sub {F : ℂ → ℂ} {C p : ℝ} (hC : 0 ≤ C)
    (hFd : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → s.im ≤ -2 → DifferentiableAt ℂ F s)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → y ≤ -2 →
      ‖F ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖)
    {σ A B : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 3 / 2) (hAB : A ≤ B) (hB : B ≤ -2) :
    ‖(∫ y in A..B, F ((σ : ℂ) + y * I) * offKernel τ ((σ : ℂ) + y * I)) -
      (∫ y in A..B, F (((3 / 2 : ℝ) : ℂ) + y * I) * offKernel τ (((3 / 2 : ℝ) : ℂ) + y * I))‖ ≤
      quantizationContourBound C p τ A + quantizationContourBound C p τ B := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  let f : ℂ → ℂ := fun s => F s * offKernel τ s
  have hcont : ContinuousOn f (uIcc σ (3 / 2) ×ℂ uIcc A B) := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le hσ1, uIcc_of_le hAB] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    exact ((hFd s (by linarith) hr2 (by linarith)).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℂ f (Ioo (min σ (3 / 2)) (max σ (3 / 2)) ×ℂ
      Ioo (min A B) (max A B)) := by
    intro s hs
    rw [Complex.mem_reProdIm, min_eq_left hσ1, max_eq_right hσ1,
      min_eq_left hAB, max_eq_right hAB] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    exact ((hFd s (by linarith) hr2.le (by linarith)).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
    ((σ : ℂ) + A * I) (((3 / 2 : ℝ) : ℂ) + B * I) (by simpa using hcont) (by simpa using hdiff)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, smul_eq_mul] at hrect
  have hedge : ∀ y : ℝ, y ≤ -2 →
      ‖∫ x in σ..(3 / 2), f ((x : ℂ) + y * I)‖ ≤ quantizationContourBound C p τ y := by
    intro y hy
    have hy2 : 1 ≤ |y| := by rw [abs_of_neg (by linarith : y < 0)]; linarith
    have hbd : ∀ x ∈ uIoc σ (3 / 2), ‖f ((x : ℂ) + y * I)‖ ≤ quantizationContourBound C p τ y := by
      intro x hx
      rw [uIoc_of_le hσ1] at hx
      rw [show f ((x : ℂ) + y * I) = F ((x : ℂ) + y * I) * offKernel τ ((x : ℂ) + y * I) from rfl, norm_mul]
      exact mul_le_mul (hF x y (by linarith [hx.1]) hx.2 hy)
        (norm_offKernel_le hτre hτ1 (by linarith [hx.1]) hx.2 hy2) (norm_nonneg _) (by positivity)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hwidth : |(3 / 2 : ℝ) - σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    exact h.trans ((mul_le_mul_of_nonneg_left hwidth (by dsimp [quantizationContourBound]; positivity)).trans_eq (mul_one _))
  let L := ∫ y in A..B, f ((σ : ℂ) + y * I)
  let R := ∫ y in A..B, f (((3 / 2 : ℝ) : ℂ) + y * I)
  let Bot := ∫ x in σ..(3 / 2), f ((x : ℂ) + A * I)
  let Top := ∫ x in σ..(3 / 2), f ((x : ℂ) + B * I)
  have he : I * (L - R) = Bot - Top := by
    dsimp [L, R, Bot, Top]
    linear_combination (-1 : ℂ) * hrect
  change ‖L - R‖ ≤ _
  calc ‖L - R‖ = ‖I * (L - R)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖Bot - Top‖ := by rw [he]
    _ ≤ ‖Bot‖ + ‖Top‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (hedge A (by linarith)) (hedge B hB)

/-- Compact radial convergence pays the critical-edge passage in the rectangle inequality. -/
theorem norm_quantization_trace_rectangle_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C p : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖)
    {A B : ℝ} (hAB : A ≤ B) (hB : B ≤ -2) :
    ‖(∫ y in A..B, quantizationTraceF hW y * pairKernel y τ) -
      (∫ y in A..B, edgeIntegrand (quantizationCompletion hW) τ (edgePt y))‖ ≤
      quantizationContourBound C p τ A + quantizationContourBound C p τ B := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  simp only [quantization_pairKernel_eq_offKernel]
  apply le_of_tendsto ((tendsto_integral_quantizationTraceF hW hτ0 A B).sub_const
    (∫ y in A..B, edgeIntegrand (quantizationCompletion hW) τ (edgePt y))).norm
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with η hη
  exact norm_quantization_open_rectangle_sub hC (fun s hs _ hi =>
    differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz) hs
      (fun h => by simp [h] at hi; linarith) (fun h => by simp [h] at hi; linarith))
    (fun x y hx hx' hy => hF x y hx hx' (by rw [abs_of_neg (by linarith)]; linarith))
    hτre hτ1 (by linarith [hη.1]) (by linarith [hη.2]) hAB hB

/-- The distant horizontal bound vanishes for each fixed point in the right half-plane. -/
theorem tendsto_quantizationContourBound (C p : ℝ) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (quantizationContourBound C p τ) atBot (𝓝 0) := by
  let δ : ℝ := τ.re / ‖τ‖
  have hδ : 0 < δ := div_pos hτ (norm_pos_iff.mpr (by intro h; rw [h] at hτ; simp at hτ))
  have ht : Tendsto (fun y : ℝ => 1 + |y|) atBot atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_abs_atBot_atTop.eventually (eventually_ge_atTop b)] with y hy
    linarith
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p δ hδ).comp ht).const_mul
    (C * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) * Real.exp δ)
  rw [mul_zero] at h
  apply h.congr
  intro y
  dsimp [quantizationContourBound]
  have he : Real.exp (-(|y| * (τ.re / ‖τ‖))) = Real.exp δ * Real.exp (-δ * (1 + |y|)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [δ]
    ring
  rw [he]
  ring

/-- Measurability and exponential damping suffice for the actual left vertical integral. -/
theorem integrableOn_quantizationTraceF_pairKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -2) :
    IntegrableOn (fun y : ℝ => quantizationTraceF hW y * pairKernel y τ) (Iic B) := by
  obtain ⟨CB, hCB, hpoly⟩ := exists_norm_quantizationTraceF_linear_le hW
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  let δ : ℝ := τ.re / ‖τ‖
  let K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖
  have hδ : 0 < δ := div_pos hτre (norm_pos_iff.mpr hτ0)
  have hdom := ((integrable_one_add_abs_pow_mul_exp hδ 1).const_mul (CB * K)).integrableOn (s := Iic B)
  refine hdom.mono' ((measurable_quantizationTraceF hW).mul
    (continuous_pairKernel hτ0).measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
  have hy' : y ≤ B := hy
  have hy1 : 1 ≤ |y| := by rw [abs_of_neg (by linarith : y < 0)]; linarith
  have hk := norm_offKernel_le hτre hτ1 (x := 1 / 2) (y := y) le_rfl (by norm_num) hy1
  rw [norm_mul, quantization_pairKernel_eq_offKernel]
  calc _ ≤ (CB * (1 + |y|)) * (K * Real.exp (-(|y| * δ))) :=
        mul_le_mul (hpoly y) hk (norm_nonneg _) (by positivity)
    _ = _ := by simp only [pow_one]; rw [mul_comm δ]; ring

/-- The actual right edge has an absolutely integrable Dirichlet majorant. -/
theorem integrableOn_quantization_rightEdge {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -2) :
    IntegrableOn (fun y : ℝ => edgeIntegrand (quantizationCompletion hW) τ (edgePt y)) (Iic B) := by
  let CS : ℝ := Real.exp (∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖)
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hFc : Continuous (fun y : ℝ => prodF (quantizationCompletion hW) (edgePt y)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hr : (edgePt y).re = 3 / 2 := edgePt_re y
    have h0 : edgePt y ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
    have h1 : edgePt y ≠ 1 := by intro h; simp [h] at hr; norm_num at hr
    exact (differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz)
      (by rw [hr]; norm_num) h0 h1).continuousAt.comp
      (f := edgePt) (show ContinuousAt edgePt y from by unfold edgePt; fun_prop)
  refine ((integrableOn_offKernel_edgePt hτre hτ1 (by linarith : B ≤ -1)).norm.const_mul CS).mono'
    ((hFc.mul (continuous_offKernel_edgePt hτ0)).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun y => ?_
  have hre : 1 < (edgePt y).re := by rw [edgePt_re]; norm_num
  have hF : ‖prodF (quantizationCompletion hW) (edgePt y)‖ ≤ CS := by
    rw [quantization_prodF_eq_zetaOf hW hre]
    simpa [CS, edgePt_re] using norm_zetaOf_le
      (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ) hre
  simp only [edgeIntegrand, norm_mul]
  exact mul_le_mul_of_nonneg_right hF (norm_nonneg _)

/-- Send the lower height to minus infinity after passing compact rectangles to the trace. -/
theorem norm_quantization_halfline_sub_right {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C p : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -2) :
    ‖(∫ y in Iic B, quantizationTraceF hW y * pairKernel y τ) -
      (∫ y in Iic B, edgeIntegrand (quantizationCompletion hW) τ (edgePt y))‖ ≤
      quantizationContourBound C p τ B := by
  have hL := intervalIntegral_tendsto_integral_Iic B
    (integrableOn_quantizationTraceF_pairKernel hW hτre hτ1 hB) tendsto_id
  have hR := intervalIntegral_tendsto_integral_Iic B
    (integrableOn_quantization_rightEdge hW hτre hτ1 hB) tendsto_id
  have hlim := (tendsto_quantizationContourBound C p hτre).add_const (quantizationContourBound C p τ B)
  rw [zero_add] at hlim
  apply le_of_tendsto_of_tendsto (hL.sub hR).norm hlim
  filter_upwards [eventually_le_atBot B] with A hA
  exact norm_quantization_trace_rectangle_sub hW hC hF hτre hτ1 hA hB

/-- The factor one half in the contour displacement is fixed by y=2t. -/
theorem norm_quantization_halfline_two_mul_sub_right {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C p : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {b : ℝ} (hb : b ≤ -1) :
    ‖(∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
      (1 / 2 : ℂ) * (∫ y in Iic (2 * b), edgeIntegrand (quantizationCompletion hW) τ (edgePt y))‖ ≤
      (1 / 2 : ℝ) * quantizationContourBound C p τ (2 * b) := by
  rw [setIntegral_Iic_comp_two_mul (fun y => quantizationTraceF hW y * pairKernel y τ) b,
    ← mul_sub, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  exact mul_le_mul_of_nonneg_left
    (norm_quantization_halfline_sub_right hW hC hF hτre hτ1 (by linarith)) (by norm_num)

/-- Subtract the resonant coefficient after the source contour passage. -/
theorem norm_quantization_radialError_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C p : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {b : ℝ} (hb : b ≤ -1) :
    ‖(∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
      dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m τ t‖ ≤ (1 / 2 : ℝ) *
      (‖∑' n, if n = m then 0 else edgeTerm (dirichletExp (lamLog lam)) τ (2 * b) n‖ +
        quantizationContourBound C p τ (2 * b)) := by
  have hc := norm_quantization_halfline_two_mul_sub_right hW hC hF hτre hτ1 hb
  have hs := hasSum_edgeTerm
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (fun _ hz => quantizationContinuation_eq_arch hW hz)
    (fun _ hz => hasDerivAt_quantizationCompletion hW hz) (quantizationCompletion_two hW)
    hτre hτ1 (B := 2 * b) (by linarith)
  have he : (∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
      dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m τ t =
      ((∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
        (1 / 2 : ℂ) * ∫ y in Iic (2 * b), edgeIntegrand (quantizationCompletion hW) τ (edgePt y)) +
      (1 / 2 : ℂ) * ∑' n, if n = m then 0 else edgeTerm (dirichletExp (lamLog lam)) τ (2 * b) n := by
    rw [← hs.tsum_eq, hs.summable.tsum_eq_add_tsum_ite m, edgeTerm_resonant _ hm]
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  linarith

/-- Refined radial remainder from the actual source, with every exponent in (0,1]. -/
theorem exists_norm_quantization_radialError_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ b : ℝ, b ≤ -1 →
      ‖(ε : ℂ) * ((∫ t in Iic b, quantizationTraceF hW (2 * t) *
          pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) -
        dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m ((ε : ℂ) + (m : ℂ) * I) t)‖ ≤
      K * ε ^ (1 - ν) * Real.exp (b * (ε / ‖(ε : ℂ) + (m : ℂ) * I‖)) := by
  obtain ⟨CF, hCF, hF⟩ := exists_quantizationProdF_subpolynomial hW hν
  have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
  have hν0 := hν.le
  have hpi := Real.pi_pos
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have h32 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by simp; norm_num
  have hSa_summ : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := (hLa _ h32).1.norm
  set Sa : ℝ := ∑' n, ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ with hSa
  have hSa0 : 0 ≤ Sa := tsum_nonneg fun n => norm_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  set K : ℝ := (1 / 2) * (Sa * M ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) +
    CF * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (1 + 2 * M)) with hK
  refine ⟨K, fun ε hε hε1 b hb => ?_⟩
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [hτ]
    rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hM]; linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := ε / ‖τ‖ with hδ
  have hδ' : τ.re / ‖τ‖ = δ := by rw [hτre]
  have hδ0 : 0 < δ := div_pos hε hτpos
  have hεδ : ε ≤ δ * M := by
    rw [hδ, div_mul_eq_mul_div, le_div_iff₀ hτpos]; nlinarith
  -- off-resonant terms
  have hite : ∀ n, ‖(if n = m then 0 else edgeTerm a τ (2 * b) n)‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
        (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) := by
    intro n
    split_ifs with hnm
    · rw [norm_zero]; positivity
    · exact norm_edgeTerm_le a hm hnm hε hε1 (B := 2 * b) (by linarith)
  have hite_summ : Summable fun n => ‖(if n = m then 0 else edgeTerm a τ (2 * b) n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hite (hSa_summ.mul_right _)
  have hoff : ‖∑' n, (if n = m then 0 else edgeTerm a τ (2 * b) n)‖ ≤
      Sa * (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) := by
    refine (norm_tsum_le_tsum_norm hite_summ).trans ?_
    rw [hSa, ← tsum_mul_right]
    exact hite_summ.tsum_le_tsum hite (hSa_summ.mul_right _)
  -- the top edge
  have h2b : 2 ≤ |2 * b| := by rw [abs_mul, abs_two, abs_of_neg (by linarith : b < 0)]; linarith
  have h2babs : |2 * b| = 2 * |b| := by rw [abs_mul, abs_two]
  have hexpb : Real.exp (-(|2 * b| * δ)) = Real.exp (2 * b * δ) := by
    rw [h2babs, abs_of_neg (by linarith : b < 0)]; congr 1; ring
  have hsource := norm_quantization_radialError_le hW hCF hF hm hτre0 hτ1 hb
  have hsum_le : ‖(∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
      a m * ∫ t in Iic b, rhoMain m τ t‖ ≤ (1 / 2 : ℝ) *
      (Sa * (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) +
        CF * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
          Real.exp (2 * b * δ))) := by
    refine hsource.trans ?_
    dsimp only [quantizationContourBound]
    rw [hδ', hexpb, h2babs]
    exact mul_le_mul_of_nonneg_left (add_le_add hoff le_rfl) (by norm_num)
  have hτs : ‖τ‖ ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hτM (by norm_num)
  have hεs : ε ≤ ε ^ (1 - ν) := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (1 - ν) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have he2 : Real.exp (2 * b * δ) ≤ Real.exp (b * δ) := Real.exp_le_exp.mpr (by nlinarith)
  have hpart2 := mul_rpow_exp_le_rpow hε hε1 hδ0 hM0 hεδ (by linarith : b ≤ 0) hν0 hν1
  have h1 : ε * Sa * ‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ) ≤
      ε ^ (1 - ν) * Sa * M ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (b * δ) := by
    gcongr
  have h2 : CF * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) *
      (ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ))) ≤
      CF * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ)) := by
    gcongr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  calc ε * ‖(∫ t in Iic b, quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) -
        a m * ∫ t in Iic b, rhoMain m τ t‖
      ≤ ε * (1 / 2 * (Sa * (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) +
          CF * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
            Real.exp (2 * b * δ)))) := mul_le_mul_of_nonneg_left hsum_le hε.le
    _ = 1 / 2 * (ε * Sa * ‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ) +
          CF * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) *
            (ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ)))) := by ring
    _ ≤ 1 / 2 * (ε ^ (1 - ν) * Sa * M ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) *
          Real.exp (b * δ) + CF * (4 * Real.pi ^ (3 / 4 : ℝ) * M) *
            (ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ))) := by linarith
    _ = K * ε ^ (1 - ν) * Real.exp (b * δ) := by rw [hK]; ring

end RHTower.WeilSpectral
