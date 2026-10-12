import GaloisForLFunctions.RHTower.KiKimLeeSharpFarTerms
import GaloisForLFunctions.RHTower.KiKimLeeLargeHeightReality

/-!
# Positivity of the Ki–Kim–Lee slope at one height, sharp window

Notation of `KiKimLeeRelativeBounds`: `α = ½ log(X/2π)`, `a = α + iπ/4`, `F(w) = ξ(½ + w + iX)`,
`u = y + 2tα`, `P = ‖F(u)‖e^{−tα²}`, `c = 2tα`, `W = c + α²`. The window starts at `½ + η`, with
model error `η₁ = 1/η + 3`.

**Theorem** (`re_slope_mul_conj_pos_sharp`). Suppose the two error sums are small:

`S₁ = sharpR1 + kklR2 + sharpR3 + sharpStripErr + e^b kklRC ≤ 1/5`,
`S₂ = 2 sharpStripErr + e^b (kklRC + kklRB) + η₁(1 + sharpR3) < (18/25) α`,

with `b = (9/2)η₁`, and suppose `1 + η ≤ c`, `3/2 ≤ c`, `m ≤ c² − 2c(1+η) + ¼` and the window fits.
Then `Re(Q' Q̄) > 0`.

**Proof.** This is `re_mul_conj_pos_of_estimates`. The main term has modulus `P e^{−tπ²/16} ≥ (23/25)P`.
`‖Q − Main‖ ≤ P·S₁` and `‖D − aQ‖ ≤ P·S₂`, from the window estimates with:
* the sharp strip terms (convexity and Gaussian decay, `sharp_strip_terms_le`);
* the Chernoff lower tail and the scaled model error;
* the window mass;
* the far terms with the split-model bound at `W`.

The slope error `η₁` enters only `S₂`, against `α`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- `‖F(W)‖ ≤ e^{(9/2)η₁} ‖F(u)‖ e^{(W−u)(α+1/8)}` for `u` in the near window and `9/2 ≤ W`. -/
theorem norm_xiLine_far_end_le {η X u W : ℝ} (hX : 200 ≤ X) (hη : 0 < η)
    (hu : u ∈ Icc (1 / 2 + η) (X / 32 - 1 / 2)) (hW9 : 9 / 2 ≤ W) (huW : u ≤ W)
    (hWX : W ≤ X / 32 - 1 / 2) :
    ‖xiLine X W‖ ≤
      (Real.exp (9 / 2 * (1 / η + 3)) * ‖xiLine X u‖) *
        Real.exp ((W - u) * ((horizontalSlope X).re + 1 / 8)) := by
  rcases le_or_gt u (9 / 2) with h9 | h9
  · have h := norm_xiLine_le_split_model hX hη ⟨hu.1, h9⟩ ⟨hW9, hWX⟩
    exact h
  · have h := norm_xiLine_le_model hX ⟨h9.le, hu.2⟩ ⟨hW9, hWX⟩
    rw [abs_of_nonneg (by linarith), mul_assoc, ← Real.exp_add] at h
    have hb : 1 ≤ Real.exp (9 / 2 * (1 / η + 3)) := Real.one_le_exp (by positivity)
    have hn : 0 ≤ ‖xiLine X u‖ * Real.exp ((W - u) * ((horizontalSlope X).re + 1 / 8)) := by
      positivity
    calc ‖xiLine X W‖ ≤ ‖xiLine X u‖ *
          Real.exp ((W - u) * (horizontalSlope X).re + 1 / 8 * (W - u)) := h
      _ = 1 * (‖xiLine X u‖ * Real.exp ((W - u) * ((horizontalSlope X).re + 1 / 8))) := by
          rw [one_mul]; congr 2; ring
      _ ≤ Real.exp (9 / 2 * (1 / η + 3)) *
            (‖xiLine X u‖ * Real.exp ((W - u) * ((horizontalSlope X).re + 1 / 8))) := by
          gcongr
      _ = _ := by ring

/-- **Positivity of `Re(Q' Q̄)` at one height, sharp window.** -/
theorem re_slope_mul_conj_pos_sharp {K η m t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hη : 0 < η)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2) (hα1 : 1 ≤ (horizontalSlope X).re)
    (hc1 : 1 + η ≤ 2 * t * (horizontalSlope X).re)
    (hc32 : 3 / 2 ≤ 2 * t * (horizontalSlope X).re)
    (hm : m ≤ (2 * t * (horizontalSlope X).re) ^ 2 -
      2 * (2 * t * (horizontalSlope X).re) * (1 + η) + 1 / 4)
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hS1 : sharpR1 η t (horizontalSlope X).re + kklR2 t (horizontalSlope X).re + sharpR3 η t +
      sharpStripErr K η m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / η + 3)) * kklRC t (horizontalSlope X).re ≤ 1 / 5)
    (hS2 : 2 * sharpStripErr K η m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / η + 3)) *
        (kklRC t (horizontalSlope X).re + kklRB t (horizontalSlope X).re) +
      (1 / η + 3) * (1 + sharpR3 η t) < 18 / 25 * (horizontalSlope X).re) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * xiLine X w) *
      starRingEnd ℂ (halfGaussTransform t (xiLine X) y)).re := by
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  set b := 9 / 2 * (1 / η + 3) with hbdef
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  have hu : u ∈ Icc (1 / 2 + η) (X / 32 - 1 / 2) :=
    ⟨by rw [hudef]; linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + η ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]
    unfold xiLine
    rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 < P := by positivity
  -- the window hypotheses
  have hmodel : ∀ w ∈ Icc (1 / 2 + η) W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp ((1 / η + 3) * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη hu ⟨hw.1, hw.2.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (1 / 2 + η) W, ‖xiLineDeriv X w - a * xiLine X w‖ ≤
      (1 / η + 3) * ‖xiLine X w‖ :=
    fun w hw => norm_xiLineDeriv_sub_le_near hX hη hw.1 (hw.2.trans hWX)
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by positivity) (by linarith) hw1W hmodel
  have hD := norm_slope_sub_mul_le ht (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by linarith) hw1W hderiv
  -- the pieces
  have hT1 := sharp_lowerTail_le (η := η) ht hy hα0 hN0
  have hT2 := upperTail_le ht hy hN0 (α := α)
  have hT3 := sharp_modelError_le (α := α) (y := y) ht hη hN0
  have hM := sharp_windowMass_le ht hη hX hu hWX
  have hcX : u ≤ X := by
    have := hu.2; linarith
  obtain ⟨hSA, hOA, hB1⟩ := sharp_strip_terms_le ht hη hK hK0 (by linarith) hy hα0 hc32 hcX hm
  have hFWb : ‖xiLine X W‖ ≤ (Real.exp b * N) * Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη hu hW9 hWu hWX
  obtain ⟨hSC, hOC, hB2⟩ := far_terms_le_of_bound (b := b) ht ht8 hX hy hα1 hW9 hFWb
  have hph := gaussPhase_ge ht8 ht
  have hR2 := kklR2_nonneg t α
  have hRC := kklRC_nonneg ht hα0 (α := α)
  have hRB := kklRB_nonneg ht (α := α)
  have hR1 : 0 ≤ sharpR1 η t α := (Real.exp_pos _).le
  have hR3 : 0 ≤ sharpR3 η t := by unfold sharpR3; positivity
  have hRS : 0 ≤ sharpStripErr K η m t α := by unfold sharpStripErr; positivity
  have heb : 0 ≤ Real.exp b := (Real.exp_pos _).le
  -- the main term
  have hmain := norm_main_eq (t := t) (X := X) (y := y) (xiLine X u)
  rw [← hadef, ← hαdef, ← hudef] at hmain
  have hmain' : ‖xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (y * a + t * a ^ 2)‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
    rw [hmain, hP, hN]
  set S₁ := sharpR1 η t α + kklR2 t α + sharpR3 η t + sharpStripErr K η m t α +
    Real.exp b * kklRC t α with hS₁
  set S₂ := 2 * sharpStripErr K η m t α + Real.exp b * (kklRC t α + kklRB t α) +
    (1 / η + 3) * (1 + sharpR3 η t) with hS₂
  refine re_mul_conj_pos_of_estimates (Main := xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (y * a + t * a ^ 2)) (E₁ := P * S₁) (E₂ := P * S₂) hα0 ?_ ?_ ?_ ?_
  · refine hQ.trans ?_
    have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
        ((∫ w in Iic (1 / 2 + η : ℝ), gaussDensity t (w - y) * Real.exp (w * a.re)) +
          (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * a.re)) +
          ∫ w, gaussDensity t (w - y) * Real.exp (w * a.re) *
            (Real.exp ((1 / η + 3) * |w - u|) - 1)) =
        N * Real.exp (-(u * α)) * (∫ w in Iic (1 / 2 + η : ℝ),
            gaussDensity t (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
            (Real.exp ((1 / η + 3) * |w - u|) - 1) := by
      ring
    rw [e]
    have hOC' : ∫ w in Ioi W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        P * (Real.exp b * kklRC t α) := by
      refine hOC.trans (le_of_eq ?_); rw [hP]; ring
    have hT1' := hT1
    have hT3' := hT3
    rw [← hudef] at hT1' hT3'
    have hsum : P * sharpR1 η t α + P * kklR2 t α + P * sharpR3 η t +
        P * sharpStripErr K η m t α + P * (Real.exp b * kklRC t α) = P * S₁ := by
      rw [hS₁]; ring
    linarith
  · refine hD.trans ?_
    have hSC' : ∫ w in Ioi W, (|(w - y) / (2 * t)| + ‖a‖) * gaussDensity t (w - y) *
        ‖xiLine X w‖ ≤ P * (Real.exp b * kklRC t α) := by
      refine hSC.trans (le_of_eq ?_); rw [hP]; ring
    have hB2' : gaussDensity t (W - y) * ‖xiLine X W‖ ≤ P * (Real.exp b * kklRB t α) := by
      refine hB2.trans (le_of_eq ?_); rw [hP]; ring
    have hM' : (1 / η + 3) * ∫ w in Ioc (1 / 2 + η) W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        (1 / η + 3) * (P * (1 + sharpR3 η t)) := by
      gcongr
    have hsum : P * sharpStripErr K η m t α + P * (Real.exp b * kklRC t α) +
        P * sharpStripErr K η m t α + P * (Real.exp b * kklRB t α) +
        (1 / η + 3) * (P * (1 + sharpR3 η t)) = P * S₂ := by
      rw [hS₂]; ring
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have : P * S₁ ≤ P * (1 / 5) := mul_le_mul_of_nonneg_left hS1 hP0.le
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have h2 : P * S₁ ≤ P * (1 / 5) := mul_le_mul_of_nonneg_left hS1 hP0.le
    have h3 : P * S₂ < P * (18 / 25 * α) := mul_lt_mul_of_pos_left hS2 hP0
    have h4 : 18 / 25 * P ≤ P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * S₁ := by linarith
    have h5 : α * (18 / 25 * P) ≤ α * (P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * S₁) :=
      mul_le_mul_of_nonneg_left h4 hα0
    have h6 : P * (18 / 25 * α) = α * (18 / 25 * P) := by ring
    linarith

end

end RHTower.DeBruijn
