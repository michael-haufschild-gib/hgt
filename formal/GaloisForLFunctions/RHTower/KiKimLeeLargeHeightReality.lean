import GaloisForLFunctions.RHTower.KiKimLeeRelativeBounds

/-!
# Large-height reality of the de Bruijn–Newman deformation (Ki–Kim–Lee)

For `0 < t ≤ 1/8` and `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx`, the reflection split
`H_t(X + iy) = Q(−y) + conj Q(y)` with `Q(y) = ∫_0^∞ g_t(w − y) ξ(½ + w + iX) dw` reduces the
reality of the zeros at height `X` to `‖Q(−y)‖ ≠ ‖Q(y)‖` for `0 < |y| ≤ ½`. At height `X` the
average `Q` is dominated by a Gaussian window around `u = y + 2tα`, `α = ½ log(X/2π)`, deep in the
Euler region, where `ξ` follows the exponential model `e^{wa}`, `a = α + iπ/4`. There

`Q' = aQ + R`,   `‖R‖ ≤ (1/8)‖window mass‖ + (terms that are o(P))`,   `‖Q‖ ≥ (0.92 − 0.43) P`,

so `Re(Q' Q̄) ≥ ‖Q‖ (α‖Q‖ − ‖R‖) > 0` (`re_slope_mul_conj_pos`), `‖Q‖²` increases on `[−½, ½]`,
and `H_t(X + iy) ≠ 0` for `0 < |y| ≤ ½` (`eventually_riemannHeat_ne_zero`). Since every zero of `H_t`
has `|Im z| < ½`, all zeros of `H_t` of large real part are real (`exists_riemannHeat_zeros_real`).
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

theorem modelConstant_le {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2) ≤ 3 / 10 := by
  have h1 : Real.exp (t * (1 + 1 / 8) ^ 2) ≤ Real.exp (81 / 512) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 := Real.exp_bound_div_one_sub_of_interval' (x := 81 / 512) (by norm_num) (by norm_num)
  norm_num at h2
  linarith

theorem gaussPhase_ge {t : ℝ} (ht8 : t ≤ 1 / 8) (ht : 0 < t) :
    23 / 25 ≤ Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
  have h := Real.add_one_le_exp (-(t * (Real.pi / 4) ^ 2))
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have : t * (Real.pi / 4) ^ 2 ≤ 1 / 8 * (3.1416 / 4) ^ 2 := by
    gcongr
  norm_num at this
  linarith

theorem horizontalSlope_im (X : ℝ) : (horizontalSlope X).im = Real.pi / 4 := by
  simp [horizontalSlope]

theorem norm_main_eq {t X y : ℝ} (N : ℂ) :
    ‖N * Complex.exp (-(((y + 2 * t * (horizontalSlope X).re : ℝ) : ℂ) * horizontalSlope X)) *
        Complex.exp (y * horizontalSlope X + t * horizontalSlope X ^ 2)‖ =
      ‖N‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, mul_assoc, ← Real.exp_add,
    mul_assoc ‖N‖ (Real.exp _), ← Real.exp_add]
  congr 2
  simp only [Complex.neg_re, Complex.add_re, pow_two, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, horizontalSlope_im]
  ring

theorem kklR1_nonneg (t α : ℝ) : 0 ≤ kklR1 t α := (Real.exp_pos _).le
theorem kklR2_nonneg (t α : ℝ) : 0 ≤ kklR2 t α := (Real.exp_pos _).le
theorem kklRA_nonneg {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α) : 0 ≤ kklRA t α := by
  unfold kklRA; positivity
theorem kklRC_nonneg {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α) : 0 ≤ kklRC t α := by
  unfold kklRC; positivity
theorem kklRB_nonneg {t α : ℝ} (ht : 0 < t) : 0 ≤ kklRB t α := by
  unfold kklRB; positivity

/-- **Positivity of `Re(Q' Q̄)`** at one height and one `y`. -/
theorem re_slope_mul_conj_pos {t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hX : 200 ≤ X)
    (hy : |y| ≤ 1 / 2) (hα1 : 1 ≤ (horizontalSlope X).re)
    (hu9 : 5 ≤ 2 * t * (horizontalSlope X).re)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hδ : kklError t (horizontalSlope X).re ≤ 1 / 8) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * xiLine X w) *
      starRingEnd ℂ (halfGaussTransform t (xiLine X) y)).re := by
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  have hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨by rw [hudef]; linarith, hWu.trans hWX⟩
  have h9W : (9 / 2 : ℝ) ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]
    unfold xiLine
    rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 < P := by positivity
  -- the two window hypotheses
  have hmodel : ∀ w ∈ Icc (9 / 2 : ℝ) W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp (1 / 8 * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le hX hu ⟨hw.1, hw.2.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (9 / 2 : ℝ) W, ‖xiLineDeriv X w - a * xiLine X w‖ ≤
      1 / 8 * ‖xiLine X w‖ := fun w hw => norm_xiLineDeriv_sub_le hX hw.1 (hw.2.trans hWX)
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by norm_num) (by norm_num) h9W hmodel
  have hD := norm_slope_sub_mul_le ht (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by norm_num) h9W hderiv
  -- the pieces
  have hT1 := lowerTail_le ht hy hα0 hN0
  have hT2 := upperTail_le ht hy hN0 (α := α)
  have hT3 := modelError_le ht hN0 (α := α) (y := y)
  have hM := windowMass_le ht hX hu hWX
  obtain ⟨hOA, hSA, hB1⟩ := strip_terms_le ht hX hy hα0 hu
  obtain ⟨hOC, hSC, hB2⟩ := far_terms_le ht ht8 hX hy hα1 hu hWX
  have hME := modelConstant_le ht ht8
  have hph := gaussPhase_ge ht8 ht
  have hRA := kklRA_nonneg ht hα0 (α := α)
  have hRC := kklRC_nonneg ht hα0 (α := α)
  have hR1 := kklR1_nonneg t α
  have hR2 := kklR2_nonneg t α
  have hRB := kklRB_nonneg ht (α := α)
  unfold kklError at hδ
  -- the main term
  have hmain := norm_main_eq (t := t) (X := X) (y := y) (xiLine X u)
  rw [← hadef, ← hαdef, ← hudef] at hmain
  have hmain' : ‖xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (y * a + t * a ^ 2)‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
    rw [hmain, hP, hN]
  refine re_mul_conj_pos_of_estimates (Main := xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (y * a + t * a ^ 2)) (E₁ := P * (3 / 10 + 1 / 8))
      (E₂ := P * (1 / 8 * (1 + 3 / 10) + 1 / 8)) hα0 ?_ ?_ ?_ ?_
  · refine hQ.trans ?_
    have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
        ((∫ w in Iic (9 / 2 : ℝ), gaussDensity t (w - y) * Real.exp (w * a.re)) +
          (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * a.re)) +
          ∫ w, gaussDensity t (w - y) * Real.exp (w * a.re) * (Real.exp (1 / 8 * |w - u|) - 1)) =
        N * Real.exp (-(u * α)) * (∫ w in Iic (9 / 2 : ℝ), gaussDensity t (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          ∫ w, gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (1 / 8 * |w - u|) - 1) := by
      ring
    rw [e]
    have : P * kklR1 t α + P * kklR2 t α + P * (2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2)) +
        P * kklRA t α + P * kklRC t α ≤ P * (3 / 10 + 1 / 8) := by
      have h1 := mul_le_mul_of_nonneg_left hME hP0.le
      have h2 := mul_le_mul_of_nonneg_left hδ hP0.le
      have h3 := mul_nonneg hP0.le hRB
      have h4 := mul_nonneg hP0.le hRA
      have h5 := mul_nonneg hP0.le hRC
      linarith
    linarith
  · refine hD.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hME hP0.le
    have h2 := mul_le_mul_of_nonneg_left hδ hP0.le
    have h3 := mul_nonneg hP0.le hR1
    have h4 := mul_nonneg hP0.le hR2
    have h5 := mul_nonneg hP0.le hRA
    have h6 := mul_nonneg hP0.le hRC
    have hMle : 1 / 8 * ∫ w in Ioc (9 / 2 : ℝ) W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        1 / 8 * (P * (1 + 2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2))) := by
      gcongr
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have hZ : 0 ≤ P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * (3 / 10 + 1 / 8) := by linarith
    have h2 : P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * (3 / 10 + 1 / 8) ≤
        α * (P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * (3 / 10 + 1 / 8)) :=
      le_mul_of_one_le_left hZ hα1
    linarith

/-- A quadratic with negative leading coefficient eventually lies below `−α`. -/
theorem eventually_quadratic_le_neg {c : ℝ} (hc : 0 < c) (b d : ℝ) :
    ∀ᶠ α in atTop, d + b * α - c * α ^ 2 ≤ -α := by
  filter_upwards [eventually_ge_atTop ((|b| + 1 + |d|) / c + 1)] with α hα
  have hα1 : 1 ≤ α := by
    have : 0 ≤ (|b| + 1 + |d|) / c := by positivity
    linarith
  have hcα : |b| + 1 + |d| ≤ c * α := by
    have := mul_le_mul_of_nonneg_left hα hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
    linarith
  have h1 : (|b| + 1 + |d|) * α ≤ c * α ^ 2 := by nlinarith
  have hb := le_abs_self b
  have hbn := neg_abs_le b
  have hd := le_abs_self d
  nlinarith [abs_nonneg d, abs_nonneg b]

theorem tendsto_mul_exp_quadratic (K : ℝ) {c : ℝ} (hc : 0 < c) (b d : ℝ) :
    Tendsto (fun α => K * Real.exp (d + b * α - c * α ^ 2)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp (tendsto_atBot_mono' atTop
    (eventually_quadratic_le_neg hc b d) tendsto_neg_atTop_atBot)
  simpa using h.const_mul K

theorem tendsto_of_le_mul_exp_quadratic {f : ℝ → ℝ} (K : ℝ) {c : ℝ} (hc : 0 < c) (b d : ℝ)
    (h0 : ∀ᶠ α in atTop, 0 ≤ f α)
    (hle : ∀ᶠ α in atTop, f α ≤ K * Real.exp (d + b * α - c * α ^ 2)) :
    Tendsto f atTop (𝓝 0) :=
  squeeze_zero' h0 hle (tendsto_mul_exp_quadratic K hc b d)

theorem tendsto_kklError {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    Tendsto (kklError t) atTop (𝓝 0) := by
  have h0 : ∀ᶠ α : ℝ in atTop, 0 ≤ α := eventually_ge_atTop 0
  -- `R1`
  have hR1 : Tendsto (kklR1 t) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic 1 (c := 3 / 4 * t) (by positivity) (5 / 2) 0
      (Eventually.of_forall fun α => kklR1_nonneg t α) (Eventually.of_forall fun α => ?_)
    rw [kklR1, one_mul]; ring_nf; exact le_rfl
  -- `R2`
  have hR2 : Tendsto (kklR2 t) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic 1 (c := 1) one_pos 0 (1 / 2 + t)
      (Eventually.of_forall fun α => kklR2_nonneg t α) (Eventually.of_forall fun α => ?_)
    rw [kklR2, one_mul]; ring_nf; exact le_rfl
  -- `RA`
  have hRA : Tendsto (kklRA t) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (9 / 2 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 * 13)
      (c := t) ht (8 + t / 4) (5 / (2 * t) + 1 / 16)
      (h0.mono fun α hα => kklRA_nonneg ht hα) (h0.mono fun α hα => ?_)
    have hx : 5 / (2 * t) + α + 1 ≤ Real.exp (5 / (2 * t) + α) :=
      Real.add_one_le_exp _
    have hy : 6 + 2 * Real.pi * Real.exp (2 * α) ≤ 13 * Real.exp (2 * α) := by
      have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * α)
      have := Real.pi_lt_d2
      nlinarith
    have hc : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
    have hp1 : 0 ≤ 5 / (2 * t) + α + 1 := by positivity
    have e : Real.exp (5 / (2 * t) + α) * Real.exp (2 * α) *
        Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8) =
        Real.exp (5 / (2 * t) + 1 / 16 + (8 + t / 4) * α - t * α ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    calc kklRA t α
        = 9 / 2 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 * ((5 / (2 * t) + α + 1) *
            (6 + 2 * Real.pi * Real.exp (2 * α)) *
            Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8)) := by rw [kklRA]; ring
      _ ≤ 9 / 2 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 * (Real.exp (5 / (2 * t) + α) *
            (13 * Real.exp (2 * α)) *
            Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8)) := by gcongr
      _ = 9 / 2 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 * 13 *
            (Real.exp (5 / (2 * t) + α) * Real.exp (2 * α) *
              Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8)) := by ring
      _ = _ := by rw [e]
  -- `RC`
  have hRC : Tendsto (kklRC t) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (2 * Real.exp 1 * 2) (c := 15 / 8 - t) (by linarith)
      (1 + 8 * t) (1 / (2 * t) + 15 / 16 + 18 * t)
      (h0.mono fun α hα => kklRC_nonneg ht hα) (h0.mono fun α hα => ?_)
    have hx : 1 / (2 * t) + α + 1 ≤ Real.exp (1 / (2 * t) + α) := Real.add_one_le_exp _
    calc kklRC t α
        = 2 * Real.exp 1 * 2 * ((1 / (2 * t) + α + 1) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
          rw [kklRC]; ring
      _ ≤ 2 * Real.exp 1 * 2 * (Real.exp (1 / (2 * t) + α) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
          gcongr
      _ = _ := by rw [← Real.exp_add]; ring_nf
  -- `RB`
  have hRB : Tendsto (kklRB t) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) (c := 1) one_pos
      0 0 (Eventually.of_forall fun α => kklRB_nonneg ht)
      ((eventually_ge_atTop (3 : ℝ)).mono fun α hα => ?_)
    rw [kklRB]
    gcongr
    have h4t : 2 ≤ 1 / (4 * t) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hsq : 2 * (α ^ 2 - 1 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 / (4 * t) := by
      have := mul_le_mul_of_nonneg_left h4t (sq_nonneg (α ^ 2 - 1 / 2))
      rw [mul_one_div] at this
      linarith
    have ha1 : 3 * α ≤ α ^ 2 := by nlinarith
    have ha2 : 3 * α ^ 2 ≤ α ^ 3 := by nlinarith
    have ha3 : 3 * α ^ 3 ≤ α ^ 4 := by nlinarith
    have hta : t * α ^ 2 ≤ α ^ 2 / 8 := by nlinarith [sq_nonneg α]
    have hexp : (α ^ 2 - 1 / 2) ^ 2 = α ^ 4 - α ^ 2 + 1 / 4 := by ring
    have hprod : (α ^ 2 + 1 / 2) * (α + 1 / 8) = α ^ 3 + α ^ 2 / 8 + α / 2 + 1 / 16 := by ring
    rw [hexp] at hsq
    rw [hexp, hprod]
    linarith
  have := (((hR1.add hR2).add (hRA.const_mul 2)).add (hRC.const_mul 2)).add hRB
  rw [show (0 : ℝ) = 0 + 0 + 2 * 0 + 2 * 0 + 0 by norm_num]
  exact this

theorem tendsto_horizontalSlope_re : Tendsto (fun X => (horizontalSlope X).re) atTop atTop := by
  simp only [horizontalSlope_re]
  exact ((Real.tendsto_log_atTop.comp
    (tendsto_id.atTop_div_const (by positivity : (0 : ℝ) < 2 * Real.pi))).atTop_div_const
      (by norm_num : (0 : ℝ) < 2))

/-- The window `[9/2, 2tα + α²]` fits below `X/32 − 1/2` once `α ≥ 5`. -/
theorem window_fits {t X : ℝ} (ht8 : t ≤ 1 / 8) (ht : 0 < t) (hX : 0 < X)
    (hα5 : 5 ≤ (horizontalSlope X).re) :
    2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2 := by
  set α := (horizontalSlope X).re with hα
  have hXe := height_eq hX
  rw [← hα] at hXe
  have he : α ^ 2 / 2 ≤ Real.exp α := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ α)
    nlinarith
  have he2 : Real.exp (2 * α) = Real.exp α * Real.exp α := by rw [← Real.exp_add]; ring_nf
  have h4 : α ^ 4 / 4 ≤ Real.exp (2 * α) := by
    rw [he2]
    have h0 : 0 ≤ α ^ 2 / 2 := by positivity
    nlinarith [mul_le_mul he he h0 (Real.exp_pos α).le]
  have ha2 : 25 ≤ α ^ 2 := by nlinarith
  have ha4 : 25 * α ^ 2 ≤ α ^ 4 := by nlinarith
  have hpi := Real.pi_gt_three
  have hX32 : 3 * α ^ 4 / 64 ≤ X / 32 := by
    rw [hXe]
    have : 3 * (α ^ 4 / 4) ≤ Real.pi * Real.exp (2 * α) := by
      have := mul_le_mul (le_of_lt hpi) h4 (by positivity) Real.pi_pos.le
      linarith
    linarith
  have hta : 2 * t * α ≤ α / 4 := by nlinarith
  nlinarith

/-- **Eventual positivity of `Re(Q'Q̄)`**, uniformly in `|y| ≤ ½`. -/
theorem eventually_re_slope_mul_conj_pos {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    ∀ᶠ X in atTop, ∀ y : ℝ, |y| ≤ 1 / 2 →
      0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) *
          xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) y)).re := by
  have hα := tendsto_horizontalSlope_re
  have hδ := ((tendsto_kklError ht ht8).comp hα).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [eventually_ge_atTop 200, hα.eventually_ge_atTop 5,
    hα.eventually_ge_atTop (5 / (2 * t)), hδ] with X hX h5 h5t hδX
  intro y hy
  have hu9 : 5 ≤ 2 * t * (horizontalSlope X).re := by
    have := mul_le_mul_of_nonneg_left h5t (by positivity : (0 : ℝ) ≤ 2 * t)
    rw [mul_div_cancel₀ _ (by positivity)] at this
    linarith
  exact re_slope_mul_conj_pos ht ht8 hX hy (by linarith) hu9
    (window_fits ht8 ht (by linarith) h5) hδX

/-- **The de Bruijn–Newman deformation has no non-real zero of small imaginary part at large
height.** For `0 < t ≤ 1/8`, eventually in `X`, `H_t(X + iy) ≠ 0` for `0 < |y| ≤ ½`. -/
theorem eventually_riemannHeat_ne_zero {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    ∀ᶠ X : ℝ in atTop, ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  filter_upwards [eventually_re_slope_mul_conj_pos ht ht8] with X hpos y hy0 hy
  set Q := halfGaussTransform t (xiLine X) with hQ
  have hQd : ∀ v ∈ Icc (-(1 / 2) : ℝ) (1 / 2), HasDerivAt Q
      (∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w) v :=
    fun v _ => hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
      (integrable_exp_mul_norm_xiLine ht X) v
  have hpos' : ∀ v ∈ Icc (-(1 / 2) : ℝ) (1 / 2), 0 < ((∫ w in Ioi (0 : ℝ),
      (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w) *
        starRingEnd ℂ (Q v)).re := fun v hv => hpos v (abs_le.mpr hv)
  have hH : riemannHeat t ((X : ℂ) + I * y) = Q (-y) + starRingEnd ℂ (Q y) :=
    riemannHeat_eq_halfGaussAverage ht X y
  rw [hH]
  apply add_conj_ne_zero_of_norm_ne
  have hy' := abs_le.mp hy
  rcases lt_or_gt_of_ne hy0 with hneg | hpos0
  · have h := norm_lt_norm_of_re_mul_conj_pos hQd hpos' (y := -y) (by linarith) (by linarith)
    rw [neg_neg] at h
    exact ne_of_gt h
  · exact ne_of_lt (norm_lt_norm_of_re_mul_conj_pos hQd hpos' hpos0 hy'.2)

theorem riemannHeat_neg {t : ℝ} (ht : 0 ≤ t) (z : ℂ) : riemannHeat t (-z) = riemannHeat t z :=
  (riemannKernel_superExp.mul_exp_sq ht).cosTransform_neg z

/-- **Large-height reality (Ki–Kim–Lee).** For every `t > 0` there is `X₀` such that every zero
of `H_t` with `|Re z| ≥ X₀` is real. -/
theorem exists_riemannHeat_zeros_real {t : ℝ} (ht : 0 < t) :
    ∃ X₀ : ℝ, ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| → z.im = 0 := by
  by_cases ht8 : t ≤ 1 / 8
  · obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventually_riemannHeat_ne_zero ht ht8)
    refine ⟨max X₀ 0, fun z hz hre => ?_⟩
    have him := riemannHeat_zeros_im_sq_le ht hz
    have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith) (by norm_num))
    have him' : |z.im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    by_contra hne
    rcases le_or_gt 0 z.re with h0 | h0
    · rw [abs_of_nonneg h0] at hre
      apply hX₀ z.re (le_of_max_le_left hre) z.im hne him'
      rw [← hz]
      congr 1
      apply Complex.ext <;> simp
    · rw [abs_of_neg h0] at hre
      apply hX₀ (-z).re (by simp; exact le_of_max_le_left hre) (-z).im (by simpa using hne)
        (by simpa using him')
      rw [← hz, ← riemannHeat_neg ht.le]
      congr 1
      apply Complex.ext <;> simp
  · exact ⟨0, fun z hz _ => riemannHeat_zeros_real (by linarith) hz⟩

end

end RHTower.DeBruijn
