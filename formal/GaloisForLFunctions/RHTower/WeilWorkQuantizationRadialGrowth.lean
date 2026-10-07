import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialBoundary
import GaloisForLFunctions.RHTower.HamburgerTruncatedRadialIntegral

/-!
# Canonical radial quotient and interior growth

The source is `WeilPositiveFull lam`. Normalize the checked primitive at its
arithmetic value at two, inherit open-strip growth by horizontal monotonicity,
and pass compact contour integrals to its measurable radial trace. No continuous
extension across the critical line is assumed.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity TruncatedRadial

/-- Normalize the canonical exponential by its actual arithmetic value at two. -/
def quantizationCompletion {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  bigG lam 2 * Complex.exp (quantizationLogPrimitive hW s)

theorem quantizationCompletion_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationCompletion hW 2 = bigG lam 2 := by
  simp [quantizationCompletion, quantizationLogPrimitive_two]

theorem hasDerivAt_quantizationCompletion {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (quantizationCompletion hW)
      (weilContinuation hW s * quantizationCompletion hW s) s := by
  exact ((hasDerivAt_quantizationLogPrimitive hW hs).cexp.const_mul (bigG lam 2)).congr_deriv
    (by simp only [quantizationCompletion]; ring)

theorem quantizationContinuation_eq_arch {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    weilContinuation hW s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := by
  rw [weilContinuation_eq hW hs, weilFunction, zetaArchimedeanDatum]
  have hf : lamC lam = lamTwo lam := by
    funext n
    unfold lamC lamTwo
    split_ifs <;> simp
  rw [hf]

theorem quantizationCompletion_eq_bigG {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : quantizationCompletion hW s = bigG lam s :=
  G_eq_bigG (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (fun _ hz => quantizationContinuation_eq_arch hW hz)
    (fun _ hz => hasDerivAt_quantizationCompletion hW hz) (quantizationCompletion_two hW) hs

def quantizationCompletedTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  bigG lam 2 * quantizationBoundaryTrace hW y

theorem tendsto_quantizationCompletedTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Tendsto (fun η : ℝ => quantizationCompletion hW (((1 / 2 + η : ℝ) : ℂ) + y * I))
      (𝓝[>] 0) (𝓝 (quantizationCompletedTrace hW y)) :=
  (tendsto_quantizationBoundaryTrace hW y).const_mul (bigG lam 2)

theorem measurable_quantizationCompletedTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Measurable (quantizationCompletedTrace hW) :=
  measurable_const.mul (measurable_quantizationBoundaryTrace hW)

theorem norm_quantizationCompletion_le_of_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (y : ℝ) {x x' : ℝ} (hx : 1 / 2 < x) (hxx : x ≤ x') :
    ‖quantizationCompletion hW ((x : ℂ) + y * I)‖ ≤
      ‖quantizationCompletion hW ((x' : ℂ) + y * I)‖ := by
  have h := monotoneOn_exp_re_quantizationLogPrimitive hW y
    (a := x - 1 / 2) (b := x' - 1 / 2) (by simp; linarith) (by simp; linarith)
    (by linarith)
  have hxid : 1 / 2 + (x - 1 / 2) = x := by ring
  have hxid' : 1 / 2 + (x' - 1 / 2) = x' := by ring
  dsimp only at h
  rw [hxid, hxid'] at h
  simpa only [quantizationCompletion, norm_mul, Complex.norm_exp] using
    mul_le_mul_of_nonneg_left h (norm_nonneg (bigG lam 2))

theorem norm_quantizationCompletedTrace_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (y : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ‖quantizationCompletedTrace hW y‖ ≤ ‖quantizationCompletion hW ((σ : ℂ) + y * I)‖ := by
  apply le_of_tendsto (tendsto_quantizationCompletedTrace hW y).norm
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < σ - 1 / 2)] with η hη
  exact norm_quantizationCompletion_le_of_le hW y (by linarith [hη.1]) (by linarith [hη.2])

theorem quantization_prodF_eq_zetaOf {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : prodF (quantizationCompletion hW) s = zetaOf lam s :=
  prodF_eq_zetaOf (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (fun _ hz => quantizationContinuation_eq_arch hW hz)
    (fun _ hz => hasDerivAt_quantizationCompletion hW hz) (quantizationCompletion_two hW) hs

/-- The strip bound is derived inside the open half-plane; no edge continuity is used. -/
theorem exists_norm_quantizationProdF_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤
        C * (1 + |y|) ^ (1 / 2 : ℝ) := by
  have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
  have hid := fun s hs => quantizationContinuation_eq_arch hW (s := s) hs
  have hGd := fun s hs => hasDerivAt_quantizationCompletion hW (s := s) hs
  have hG2 := quantizationCompletion_two hW
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  refine ⟨4 * Real.exp 3 * Real.exp S, by positivity, fun x y hx1 hx2 hy => ?_⟩
  set s : ℂ := (x : ℂ) + (y : ℂ) * I with hs
  set s₃ : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs₃
  have hs₃re : 1 < s₃.re := by simp [hs₃]; norm_num
  have hmono : ‖(quantizationCompletion hW) s‖ ≤ ‖(quantizationCompletion hW) s₃‖ :=
    norm_quantizationCompletion_le_of_le hW y hx1 hx2
  have hG3 : ‖(quantizationCompletion hW) s₃‖ = ‖s₃‖ * ‖s₃ - 1‖ * ‖Complex.Gammaℝ s₃‖ * ‖zetaOf lam s₃‖ := by
    rw [G_eq_bigG hsl hid hGd hG2 hs₃re]; unfold bigG; rw [norm_mul, norm_mul, norm_mul]
  have hz : ‖zetaOf lam s₃‖ ≤ Real.exp S := by
    have h := norm_zetaOf_le hsl hs₃re
    have hre : (s₃.re : ℂ) = ((3 / 2 : ℝ) : ℂ) := by simp [hs₃]
    rwa [hre] at h
  have hΓ := norm_Gammaℝ_three_halves_le hx1.le hx2 hy
  have hyabs : 0 < |y| := by linarith
  have hsy : |y| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; simpa [hs] using this
  have hs1y : |y| ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simpa [hs] using this
  have hs₃n : ‖s₃‖ ≤ 2 * ‖s‖ := by
    have h := norm_add_le (((3 / 2 : ℝ) : ℂ)) ((y : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
    linarith
  have hs₃1 : ‖s₃ - 1‖ ≤ 2 * ‖s - 1‖ := by
    have e : s₃ - 1 = ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by rw [hs₃]; push_cast; ring
    have h := norm_add_le (((1 / 2 : ℝ) : ℂ)) ((y : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
    rw [e]; linarith
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hyabs hsy
  have hs10 : 0 < ‖s - 1‖ := lt_of_lt_of_le hyabs hs1y
  have hΓ0 : 0 < ‖Complex.Gammaℝ s‖ :=
    norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by simp [hs]; linarith))
  unfold prodF
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (by positivity)]
  calc ‖(quantizationCompletion hW) s‖ ≤ ‖(quantizationCompletion hW) s₃‖ := hmono
    _ = ‖s₃‖ * ‖s₃ - 1‖ * ‖Complex.Gammaℝ s₃‖ * ‖zetaOf lam s₃‖ := hG3
    _ ≤ (2 * ‖s‖) * (2 * ‖s - 1‖) *
          (Real.exp 3 * (1 + |y|) ^ (1 / 2 : ℝ) * ‖Complex.Gammaℝ s‖) * Real.exp S := by
        gcongr
    _ = 4 * Real.exp 3 * Real.exp S * (1 + |y|) ^ (1 / 2 : ℝ) *
          (‖s‖ * ‖s - 1‖ * ‖Complex.Gammaℝ s‖) := by ring

/-- The critical-line quotient uses the actual radial trace at every height. -/
def quantizationTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  quantizationCompletedTrace hW y /
    ((((1 / 2 : ℝ) : ℂ) + y * I) * ((((1 / 2 : ℝ) : ℂ) + y * I) - 1) *
      Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + y * I))

def quantizationRightMajorant {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  quantizationCompletion hW (((3 / 2 : ℝ) : ℂ) + s.im * I) /
    (s * (s - 1) * Complex.Gammaℝ s)

theorem continuousAt_quantizationRightMajorant {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 4) :
    ContinuousAt (quantizationRightMajorant hW) s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have h1 : s ≠ 1 := by intro h; simp [h] at hs'; linarith
  have hc : ContinuousAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    (continuousAt_id.mul (continuousAt_id.sub continuousAt_const)).mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith)).continuousAt
  have hr : Continuous (fun z : ℂ => (((3 / 2 : ℝ) : ℂ) + z.im * I)) := by fun_prop
  exact ((hasDerivAt_quantizationCompletion hW (s := (((3 / 2 : ℝ) : ℂ) + s.im * I))
    (by norm_num)).continuousAt.comp (f := fun z : ℂ => (((3 / 2 : ℝ) : ℂ) + z.im * I))
    hr.continuousAt).div hc (denom_ne_zero (by linarith) h0 h1)

theorem tendsto_quantizationTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Tendsto (fun η : ℝ => prodF (quantizationCompletion hW)
      (((1 / 2 + η : ℝ) : ℂ) + y * I)) (𝓝[>] 0) (𝓝 (quantizationTraceF hW y)) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + y * I
  have hs : s.re = 1 / 2 := by simp [s]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  have hc : ContinuousAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    (continuousAt_id.mul (continuousAt_id.sub continuousAt_const)).mul
      (differentiableAt_Gammaℝ_of_re_pos (by rw [hs]; norm_num)).continuousAt
  have hp : Continuous (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) := by fun_prop
  have ht : Tendsto (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) (𝓝[>] 0) (𝓝 s) := by
    simpa [s] using (hp.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (tendsto_quantizationCompletedTrace hW y).div (hc.tendsto.comp ht)
    (denom_ne_zero (by rw [hs]; norm_num) h0 h1)

theorem measurable_quantizationTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Measurable (quantizationTraceF hW) := by
  have hc : Continuous (fun y : ℝ =>
      (((1 / 2 : ℝ) : ℂ) + y * I) * ((((1 / 2 : ℝ) : ℂ) + y * I) - 1) *
        Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + y * I)) := by
    apply Continuous.mul (by fun_prop)
    rw [continuous_iff_continuousAt]
    intro y
    exact (differentiableAt_Gammaℝ_of_re_pos (s := (((1 / 2 : ℝ) : ℂ) + y * I))
      (by norm_num)).continuousAt.comp (f := fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * I))
      (show ContinuousAt (fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * I)) y from by fun_prop)
  exact (measurable_quantizationCompletedTrace hW).div hc.measurable

theorem norm_quantizationTraceF_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    ‖quantizationTraceF hW y‖ ≤
      ‖quantizationRightMajorant hW (((1 / 2 : ℝ) : ℂ) + y * I)‖ := by
  simp only [quantizationTraceF, quantizationRightMajorant, norm_div]
  have him : ((((1 / 2 : ℝ) : ℂ) + y * I) : ℂ).im = y := by simp
  rw [him]
  exact div_le_div_of_nonneg_right (norm_quantizationCompletedTrace_le hW y (by norm_num))
    (norm_nonneg _)

theorem exists_bound_quantizationTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ uIcc a b, ‖quantizationTraceF hW y‖ ≤ B := by
  have hc : Continuous (fun y : ℝ =>
      quantizationRightMajorant hW (((1 / 2 : ℝ) : ℂ) + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_quantizationRightMajorant hW (s := (((1 / 2 : ℝ) : ℂ) + y * I))
      (by simp) (by norm_num)).comp (f := fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * I))
      (show ContinuousAt (fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * I)) y from by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun y hy => ?_⟩
  exact (norm_quantizationTraceF_le hW y).trans ((hB y hy).trans (le_max_left _ _))

theorem intervalIntegrable_quantizationTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a b : ℝ) : IntervalIntegrable (quantizationTraceF hW) volume a b := by
  obtain ⟨B, _, hB⟩ := exists_bound_quantizationTraceF hW a b
  apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := B))
    (measurable_quantizationTraceF hW).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  exact hB y (uIoc_subset_uIcc hy)

theorem norm_quantizationProdF_le_rightMajorant {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs' : s.re ≤ 3 / 2) :
    ‖prodF (quantizationCompletion hW) s‖ ≤ ‖quantizationRightMajorant hW s‖ := by
  simp only [prodF, quantizationRightMajorant, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  simpa only [Complex.re_add_im] using norm_quantizationCompletion_le_of_le hW s.im hs hs'

theorem continuous_quantizationProdF_slice {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ' : σ < 1) :
    Continuous (fun y : ℝ => prodF (quantizationCompletion hW) ((σ : ℂ) + y * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hre : (((σ : ℂ) + y * I) : ℂ).re = σ := by simp
  have h0 : (σ : ℂ) + y * I ≠ 0 := by
    intro h; rw [h] at hre; simp at hre; linarith
  have h1 : (σ : ℂ) + y * I ≠ 1 := by
    intro h; rw [h] at hre; simp at hre; linarith
  exact (differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz)
    (by rw [hre]; exact hσ) h0 h1).continuousAt.comp (f := fun y : ℝ => ((σ : ℂ) + y * I))
      (show ContinuousAt (fun y : ℝ => ((σ : ℂ) + y * I)) y from by fun_prop)

/-- A compact majorant survives even when the critical-line trace is discontinuous. -/
theorem exists_bound_quantizationRadialProduct {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτ : τ ≠ 0) (a b : ℝ) :
    ∃ B : ℝ, ∀ η ∈ Ioo (0 : ℝ) (1 / 4), ∀ y ∈ uIcc a b,
      ‖prodF (quantizationCompletion hW) (((1 / 2 + η : ℝ) : ℂ) + y * I) *
        offKernel τ (((1 / 2 + η : ℝ) : ℂ) + y * I)‖ ≤ B := by
  let K : Set ℂ := Icc (1 / 2 : ℝ) (3 / 4) ×ℂ uIcc a b
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_uIcc
  have hc : ContinuousOn (fun s : ℂ => quantizationRightMajorant hW s * offKernel τ s) K := by
    intro s hs
    change s.re ∈ Icc (1 / 2 : ℝ) (3 / 4) ∧ s.im ∈ uIcc a b at hs
    exact ((continuousAt_quantizationRightMajorant hW hs.1.1 hs.1.2).mul
      (differentiableAt_offKernel hτ (by linarith [hs.1.1])
        (by linarith [hs.1.2])).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨B, fun η hη y hy => ?_⟩
  set s : ℂ := (((1 / 2 + η : ℝ) : ℂ) + y * I)
  have hre : s.re = 1 / 2 + η := by simp [s]
  have him : s.im = y := by simp [s]
  have hs : s ∈ K := by
    change s.re ∈ Icc (1 / 2 : ℝ) (3 / 4) ∧ s.im ∈ uIcc a b
    rw [hre, him]
    exact ⟨⟨by linarith [hη.1], by linarith [hη.2]⟩, hy⟩
  apply le_trans _ (hB s hs)
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_quantizationProdF_le_rightMajorant hW (by rw [hre]; linarith [hη.1])
      (by rw [hre]; linarith [hη.2])) (norm_nonneg _)

theorem tendsto_integral_quantizationTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτ : τ ≠ 0) (a b : ℝ) :
    Tendsto (fun η : ℝ => ∫ y in a..b,
      prodF (quantizationCompletion hW) (((1 / 2 + η : ℝ) : ℂ) + y * I) *
        offKernel τ (((1 / 2 + η : ℝ) : ℂ) + y * I)) (𝓝[>] 0)
      (𝓝 (∫ y in a..b, quantizationTraceF hW y *
        offKernel τ (((1 / 2 : ℝ) : ℂ) + y * I))) := by
  obtain ⟨B, hB⟩ := exists_bound_quantizationRadialProduct hW hτ a b
  have hη : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · filter_upwards [hη] with η hη
    have hc : Continuous (fun y : ℝ =>
        offKernel τ (((1 / 2 + η : ℝ) : ℂ) + y * I)) := by
      rw [continuous_iff_continuousAt]
      intro y
      exact (differentiableAt_offKernel hτ (s := (((1 / 2 + η : ℝ) : ℂ) + y * I))
        (by simp; linarith [hη.1]) (by simp; linarith [hη.2])).continuousAt.comp
        (f := fun y : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I))
        (show ContinuousAt (fun y : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) y from by fun_prop)
    exact ((continuous_quantizationProdF_slice hW (by linarith [hη.1])
      (by linarith [hη.2])).mul hc).aestronglyMeasurable.restrict
  · filter_upwards [hη] with η hη
    exact Eventually.of_forall fun y hy => hB η hη y (uIoc_subset_uIcc hy)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun y _ => ?_
    have hp : Continuous (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) := by fun_prop
    have ht : Tendsto (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) (𝓝[>] 0)
        (𝓝 (((1 / 2 : ℝ) : ℂ) + y * I)) := by
      simpa using (hp.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (tendsto_quantizationTraceF hW y).mul
      ((differentiableAt_offKernel hτ (by norm_num)
        (by norm_num)).continuousAt.tendsto.comp ht)

end RHTower.WeilSpectral
