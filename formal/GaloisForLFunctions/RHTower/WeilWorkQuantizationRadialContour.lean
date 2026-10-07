import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialGrowth

/-!
# Signed radial truncation for the canonical Weil source

Interior rectangles give a bound uniform in the left edge and truncation height.
Compact radial convergence then pays the critical-edge passage. The final source
bounds use only Weil positivity; no boundary continuity or atomic support is
supplied. These are the contour prerequisites of the finite-remainder argument,
not a proof of spectral quantization.
-/

open Complex Filter Topology Set MeasureTheory
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial

/-- Signed cancellation on interior rectangles, uniformly in the left edge. -/
theorem exists_bound_open_rectangle {F : ℂ → ℂ} {CF CS : ℝ} (hCF : 0 ≤ CF) (hCS : 0 ≤ CS)
    (hFd : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → s.im ≤ -2 → DifferentiableAt ℂ F s)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → y ≤ -2 →
      ‖F ((x : ℂ) + y * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ))
    (hR : ∀ y : ℝ, y ≤ -2 → ‖F (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ CS)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 3 / 2 → ∀ A : ℝ, A ≤ -2 →
      ‖(ε : ℂ) * ∫ y in A..(-2), F ((σ : ℂ) + y * I) *
        offKernel ((ε : ℂ) + (m : ℂ) * I) ((σ : ℂ) + y * I)‖ ≤ B := by
  have hpi := Real.pi_pos
  set K₀ : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set M : ℝ := (m : ℝ) + 1 with hM
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set B : ℝ := CS * K₀ * M ^ 2 + 2 * (CF * K₀ * M * (1 + M)) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨B, hB0, fun ε hε hε1 σ hσ hσ1 A hA => ?_⟩
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτim : τ.im = m := by simp [hτ]
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    rw [hτim, abs_of_nonneg (Nat.cast_nonneg m)] at h
    linarith
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hM]; linarith
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ1; norm_num at hτ1
  have hτpos : 0 < ‖τ‖ := by linarith
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre0 hτpos
  have hεδ : ε * δ⁻¹ = ‖τ‖ := by rw [hδ, hτre]; field_simp
  set h : ℂ → ℂ := fun s => F s * offKernel τ s with hh
  have hcont : ContinuousOn h (uIcc σ (3 / 2) ×ℂ uIcc A (-2)) := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le hσ1, uIcc_of_le hA] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    exact ((hFd s (by linarith) hr2 hi2).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℂ h (Ioo (min σ (3 / 2)) (max σ (3 / 2)) ×ℂ
      Ioo (min A (-2)) (max A (-2))) := by
    intro s hs
    rw [Complex.mem_reProdIm, min_eq_left hσ1, max_eq_right hσ1,
      min_eq_left hA, max_eq_right hA] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    exact ((hFd s (by linarith) hr2.le hi2.le).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).differentiableWithinAt
  set z : ℂ := (σ : ℂ) + (A : ℂ) * I with hz
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * I with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = A := by simp [hz]
  have hwre : w.re = 3 / 2 := by simp [hw]
  have hwim : w.im = -2 := by simp [hw]
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn h z w
    (by rw [hzre, hwre, hzim, hwim]; exact hcont)
    (by rw [hzre, hwre, hzim, hwim]; exact hdiff)
  rw [hzre, hwre, hzim, hwim] at hrect
  set L : ℂ := ∫ y in A..(-2), h ((σ : ℂ) + y * I) with hL
  set R : ℂ := ∫ y in A..(-2), h (((3 / 2 : ℝ) : ℂ) + y * I) with hRdef
  set Bot : ℂ := ∫ x in σ..(3 / 2), h ((x : ℂ) + (A : ℂ) * I) with hBot
  set Top : ℂ := ∫ x in σ..(3 / 2), h ((x : ℂ) + ((-2 : ℝ) : ℂ) * I) with hTop
  have hLnorm : ‖L‖ ≤ ‖Bot‖ + ‖Top‖ + ‖R‖ := by
    have e : I * L = Bot - Top + I * R := by
      simp only [smul_eq_mul] at hrect
      linear_combination (-1 : ℂ) * hrect
    have hIL : ‖I * L‖ = ‖L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [← hIL, e]
    calc ‖Bot - Top + I * R‖ ≤ ‖Bot - Top‖ + ‖I * R‖ := norm_add_le _ _
      _ ≤ ‖Bot‖ + ‖Top‖ + ‖R‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le Bot Top]
  have hRb : ε * ‖R‖ ≤ CS * K₀ * M ^ 2 := by
    have hbd : ∀ᵐ y ∂volume, y ∈ Ioc A (-2) →
        ‖h (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ CS * K₀ * ‖τ‖ * Real.exp (δ * y) := by
      refine Eventually.of_forall fun y hy => ?_
      have hy0 : y < 0 := by linarith [hy.2]
      have hy2 : 1 ≤ |y| := by rw [abs_of_neg hy0]; linarith [hy.2]
      have hk := norm_offKernel_le hτre0 hτ1 (x := 3 / 2) (y := y)
        (by norm_num) (by norm_num) hy2
      rw [abs_of_neg hy0] at hk
      simp only [hh]
      rw [norm_mul]
      calc ‖F (((3 / 2 : ℝ) : ℂ) + y * I)‖ * ‖offKernel τ (((3 / 2 : ℝ) : ℂ) + y * I)‖
          ≤ CS * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
            Real.exp (-(-y * (τ.re / ‖τ‖)))) := mul_le_mul (hR y hy.2) hk (norm_nonneg _) hCS
        _ = CS * K₀ * ‖τ‖ * Real.exp (δ * y) := by rw [hK₀, hδ]; ring_nf
    have hint : IntervalIntegrable (fun y => CS * K₀ * ‖τ‖ * Real.exp (δ * y)) volume A (-2) :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hA hbd hint
    rw [intervalIntegral.integral_const_mul] at h1
    have h2 := integral_exp_mul_le (A := A) (B := -2) (by norm_num) hδ0
    have hc : 0 ≤ CS * K₀ * ‖τ‖ := by positivity
    calc ε * ‖R‖ ≤ ε * (CS * K₀ * ‖τ‖ * δ⁻¹) := by
          gcongr; exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)
      _ = CS * K₀ * ‖τ‖ * (ε * δ⁻¹) := by ring
      _ = CS * K₀ * ‖τ‖ ^ 2 := by rw [hεδ]; ring
      _ ≤ CS * K₀ * M ^ 2 := by gcongr
  have hedge : ∀ y : ℝ, y ≤ -2 →
      ε * ‖∫ x in σ..(3 / 2), h ((x : ℂ) + y * I)‖ ≤ CF * K₀ * M * (1 + M) := by
    intro y hy
    have hy0 : y < 0 := by linarith
    have hy2 : 2 ≤ |y| := by rw [abs_of_neg hy0]; linarith
    have hbd : ∀ x ∈ uIoc σ (3 / 2), ‖h ((x : ℂ) + y * I)‖ ≤
        CF * (1 + |y|) ^ (1 / 2 : ℝ) * (K₀ * ‖τ‖ * Real.exp (-(|y| * δ))) := by
      intro x hx
      rw [uIoc_of_le hσ1] at hx
      have hF' := hF x y (by linarith [hx.1]) hx.2 hy
      have hk := norm_offKernel_le hτre0 hτ1 (x := x) (y := y)
        (by linarith [hx.1]) hx.2 (by linarith)
      simp only [hh]
      rw [norm_mul]
      exact mul_le_mul hF' hk (norm_nonneg _) (by positivity)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hwidth : |(3 / 2 : ℝ) - σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    have h1' : ‖∫ x in σ..(3 / 2), h ((x : ℂ) + y * I)‖ ≤
        CF * (1 + |y|) ^ (1 / 2 : ℝ) * (K₀ * ‖τ‖ * Real.exp (-(|y| * δ))) := by
      exact h1.trans ((mul_le_mul_of_nonneg_left hwidth (by positivity)).trans_eq (mul_one _))
    have h2 := mul_rpow_half_exp_le (ε := ε) (u := |y|) hε.le (abs_nonneg y) hδ0
    calc ε * ‖∫ x in σ..(3 / 2), h ((x : ℂ) + y * I)‖
        ≤ ε * (CF * (1 + |y|) ^ (1 / 2 : ℝ) * (K₀ * ‖τ‖ * Real.exp (-(|y| * δ)))) := by gcongr
      _ = CF * K₀ * ‖τ‖ * (ε * ((1 + |y|) ^ (1 / 2 : ℝ) * Real.exp (-(|y| * δ)))) := by ring
      _ ≤ CF * K₀ * ‖τ‖ * (ε + ε * δ⁻¹) := by gcongr
      _ ≤ CF * K₀ * M * (1 + M) := by
          rw [hεδ]
          have : ε + ‖τ‖ ≤ 1 + M := by linarith
          gcongr
  have hBot' := hedge A hA
  have hTop' := hedge (-2) le_rfl
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  change ε * ‖L‖ ≤ B
  calc ε * ‖L‖ ≤ ε * ‖Bot‖ + ε * ‖Top‖ + ε * ‖R‖ := by
        have := mul_le_mul_of_nonneg_left hLnorm hε.le; linarith
    _ ≤ CF * K₀ * M * (1 + M) + CF * K₀ * M * (1 + M) + CS * K₀ * M ^ 2 := by gcongr
    _ = B := by rw [hB]; ring

open WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- The arithmetic right edge pays the uniform signed estimate for the canonical trace. -/
theorem exists_bound_quantizationTraceF_below {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ A : ℝ, A ≤ -2 →
      ‖(ε : ℂ) * ∫ y in A..(-2), quantizationTraceF hW y *
        offKernel ((ε : ℂ) + (m : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ B := by
  obtain ⟨CF, hCF, hF⟩ := exists_norm_quantizationProdF_le hW
  let CS : ℝ := Real.exp (∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖)
  have hFd : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → s.im ≤ -2 →
      DifferentiableAt ℂ (prodF (quantizationCompletion hW)) s := by
    intro s hs _ hi
    have h0 : s ≠ 0 := by intro h; simp [h] at hi; linarith
    have h1 : s ≠ 1 := by intro h; simp [h] at hi; linarith
    exact differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz) hs h0 h1
  have hR : ∀ y : ℝ, y ≤ -2 →
      ‖prodF (quantizationCompletion hW) (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ CS := by
    intro y _
    have hre : (1 : ℝ) < ((((3 / 2 : ℝ) : ℂ) + y * I) : ℂ).re := by simp; norm_num
    rw [quantization_prodF_eq_zetaOf hW hre]
    simpa [CS] using norm_zetaOf_le
      (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ) hre
  obtain ⟨B, hB0, hB⟩ := exists_bound_open_rectangle hCF (Real.exp_pos _).le hFd
    (fun x y hx hx' hy => hF x y hx hx' (by rw [abs_of_neg (by linarith)]; linarith)) hR hm
  refine ⟨B, hB0, fun ε hε hε1 A hA => ?_⟩
  have hτ : (ε : ℂ) + (m : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  apply le_of_tendsto ((tendsto_integral_quantizationTraceF hW hτ A (-2)).const_mul (ε : ℂ)).norm
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with η hη
  exact hB ε hε hε1 (1 / 2 + η) (by linarith [hη.1]) (by linarith [hη.2]) A hA

theorem quantization_pairKernel_eq_offKernel (y : ℝ) (τ : ℂ) :
    pairKernel y τ = offKernel τ (((1 / 2 : ℝ) : ℂ) + y * I) := by
  rw [pairKernel_eq_offKernel]
  congr 1
  unfold HamburgerStability.linePt
  push_cast
  ring

/-- Truncation heights may approach minus infinity at any rate relative to epsilon. -/
theorem exists_bound_quantization_signed_truncation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ A : ℝ, A ≤ 0 →
      ‖(ε : ℂ) * ∫ y in A..0, quantizationTraceF hW y *
        pairKernel y ((ε : ℂ) + (m : ℂ) * I)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_quantizationTraceF_below hW hm
  obtain ⟨C, hC0, hC⟩ := exists_bound_quantizationTraceF hW (-2) 0
  refine ⟨B + 6 * C, by positivity, fun ε hε hε1 A hA => ?_⟩
  let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
  have hτre : 0 < τ.re := by simpa [τ] using hε
  have hτ0 : τ ≠ 0 := by intro h; simp [h] at hτre
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [τ]
    rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact hm1.trans h
  have hk : ∀ y : ℝ, ‖pairKernel y τ‖ ≤ 3 := by
    intro y
    have h1 : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
    have h2 : Real.exp (-(|y| * (τ.re / ‖τ‖))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (abs_nonneg _) (by positivity)))
    calc ‖pairKernel y τ‖ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(|y| * (τ.re / ‖τ‖))) := norm_pairKernel_le y hτre
      _ ≤ 3 * 1 * 1 := by gcongr
      _ = 3 := by norm_num
  let f : ℝ → ℂ := fun y => quantizationTraceF hW y * pairKernel y τ
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    (intervalIntegrable_quantizationTraceF hW a b).mul_continuousOn
      (continuous_pairKernel hτ0).continuousOn
  have hnear : ∀ a : ℝ, -2 ≤ a → a ≤ 0 → ‖(ε : ℂ) * ∫ y in a..0, f y‖ ≤ 6 * C := by
    intro a ha ha0
    have hbd : ∀ y ∈ uIoc a 0, ‖f y‖ ≤ 3 * C := by
      intro y hy
      rw [uIoc_of_le ha0] at hy
      have hy' : y ∈ uIcc (-2 : ℝ) 0 := by
        rw [uIcc_of_le (by norm_num)]
        exact ⟨by linarith [hy.1], hy.2⟩
      calc ‖f y‖ = ‖quantizationTraceF hW y‖ * ‖pairKernel y τ‖ := norm_mul _ _
        _ ≤ C * 3 := mul_le_mul (hC y hy') (hk y) (norm_nonneg _) hC0
        _ = 3 * C := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hw : |0 - a| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have hεnorm : ‖(ε : ℂ)‖ = ε := by simp [abs_of_pos hε]
    rw [norm_mul, hεnorm]
    calc ε * ‖∫ y in a..0, f y‖ ≤ 1 * ((3 * C) * 2) :=
          mul_le_mul hε1 (h.trans (mul_le_mul_of_nonneg_left hw (by positivity)))
            (norm_nonneg _) zero_le_one
      _ = 6 * C := by ring
  rcases le_or_gt (-2) A with hA2 | hA2
  · exact (hnear A hA2 hA).trans (by linarith)
  have hsplit : (∫ y in A..0, f y) = (∫ y in A..(-2), f y) + ∫ y in (-2 : ℝ)..0, f y :=
    (intervalIntegral.integral_add_adjacent_intervals (hint A (-2)) (hint (-2) 0)).symm
  have hbelow : ‖(ε : ℂ) * ∫ y in A..(-2), f y‖ ≤ B := by
    simpa only [f, quantization_pairKernel_eq_offKernel] using hB ε hε hε1 A hA2.le
  change ‖(ε : ℂ) * ∫ y in A..0, f y‖ ≤ _
  rw [hsplit, mul_add]
  exact (norm_add_le _ _).trans (add_le_add hbelow (hnear (-2) le_rfl (by norm_num)))

/-- Paper normalization: the critical height is twice the Mellin variable. -/
theorem exists_bound_quantization_signed_truncation_two_mul {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ} (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ a : ℝ, a ≤ 0 →
      ‖(ε : ℂ) * ∫ t in a..0, quantizationTraceF hW (2 * t) *
        pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_quantization_signed_truncation hW hm
  refine ⟨B / 2, by positivity, fun ε hε hε1 a ha => ?_⟩
  let f : ℝ → ℂ := fun y => quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I)
  have hchange := intervalIntegral.integral_comp_mul_left f (a := a) (b := 0) (two_ne_zero' ℝ)
  simp only [mul_zero] at hchange
  have hb := hB ε hε hε1 (2 * a) (by linarith)
  change ‖(ε : ℂ) * ∫ y in (2 * a)..0, f y‖ ≤ B at hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hb
  change ‖(ε : ℂ) * ∫ t in a..0, f (2 * t)‖ ≤ B / 2
  rw [hchange, real_smul, ← mul_assoc, mul_comm (ε : ℂ), mul_assoc, norm_mul]
  norm_num [abs_of_pos hε]
  linarith

/-- Fixed windows vanish after radial rescaling; no limit of the kernel on its cut is needed. -/
theorem tendsto_quantization_signed_fixed_truncation {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ} (hm : 1 ≤ m) (a b : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in a..b, quantizationTraceF hW y *
      pairKernel y ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_quantizationTraceF hW a b
  refine squeeze_zero_norm' (a := fun ε : ℝ => ε * (3 * C * |b - a|)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
    have hτre : 0 < τ.re := by simpa [τ] using hε
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [τ]
      rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      exact hm1.trans h
    have hk : ∀ y : ℝ, ‖pairKernel y τ‖ ≤ 3 := by
      intro y
      have h1 : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
      have h2 : Real.exp (-(|y| * (τ.re / ‖τ‖))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (abs_nonneg _) (by positivity)))
      calc ‖pairKernel y τ‖ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(|y| * (τ.re / ‖τ‖))) := norm_pairKernel_le y hτre
        _ ≤ 3 * 1 * 1 := by gcongr
        _ = 3 := by norm_num
    have hi : ‖∫ y in a..b, quantizationTraceF hW y * pairKernel y τ‖ ≤ 3 * C * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      rw [norm_mul]
      calc ‖quantizationTraceF hW y‖ * ‖pairKernel y τ‖ ≤ C * 3 :=
            mul_le_mul (hC y (uIoc_subset_uIcc hy)) (hk y) (norm_nonneg _) hC0
        _ = 3 * C := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left hi hε.le
  · have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ht.mul_const (3 * C * |b - a|)

end RHTower.WeilSpectral
