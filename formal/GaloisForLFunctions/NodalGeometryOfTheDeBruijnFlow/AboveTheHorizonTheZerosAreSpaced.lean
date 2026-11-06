import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheHalfGaussAboveTheHorizon

/-!
# Above the horizon the zeros are spaced

The central inequality holds above the collision-free horizon. For `t log(x/2π) ≥ 6600/9991 + ε` and `t log x ≤ 1`, any two real zeros `x < x'` of `H_t` satisfy
`x' − x ≥ c/log x` (`exists_gap_ge_above_horizon`).

At a zero the amplitude sits entirely in the derivative, so `|H_t'(x)| ≥ αP/2`, by the quadrature bound. On discs of radius `1/α` the flow is at most a constant times `P`, by the half-Gauss estimates
on the vertical lines; so `|H_t″| ≪ α²P` by Cauchy. A second zero closer than `≍ 1/α` would contradict the mean value theorem. In particular the constant of the central inequality exists in this zone
(`exists_central_inequality_above_horizon`), and it is a boundary condition for the gaps below the horizon.
-/

open Complex MeasureTheory Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- On vertical lines the flow is at most a constant times the amplitude, over distance `≍ 1/α`. -/
theorem exists_norm_riemannHeat_le_amp {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ X₁ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 40 ∧ 200 ≤ X₁ ∧ ∀ t ξ η : ℝ, 0 < t → t ≤ 1 / 8 → X₁ ≤ ξ →
      6600 / 9991 + ε ≤ 2 * t * (horizontalSlope ξ).re → 2 * t * (horizontalSlope ξ).re ≤ 1 → |η| ≤ δ₀ →
      |η| * (horizontalSlope ξ).re ≤ 3 →
      ‖riemannHeat t ((ξ : ℂ) + I * η)‖ ≤ 12 / 5 * Real.exp 4 * horizonAmp t ξ := by
  obtain ⟨κ, δ₁, X₁, hκ, hδ₁, hX₁, hest⟩ := exists_halfGauss_estimates hε
  refine ⟨min δ₁ (1 / 40), X₁, by positivity, min_le_right _ _, hX₁, ?_⟩
  intro t ξ η ht ht8 hξ hc1 hc2 hη hηα
  have hη1 : |η| ≤ δ₁ := hη.trans (min_le_left _ _)
  have hη2 : |η| ≤ 1 / 40 := hη.trans (min_le_right _ _)
  have hξ200 : 200 ≤ ξ := hX₁.trans hξ
  have hbound (v : ℝ) (hv : |v| = |η|) : ‖halfGaussTransform t (xiLine ξ) v‖ ≤ 6 / 5 * Real.exp 4 * horizonAmp t ξ := by
    have hv1 : |v| ≤ δ₁ := by rw [hv]; exact hη1
    obtain ⟨-, hup, -⟩ := hest t ξ v ht ht8 hξ hc1 hc2 hv1
    have hc0 : (6600 : ℝ) / 9991 ≥ 661 / 1001 := by norm_num
    have hvb := abs_le.mp (by rw [hv]; exact hη2 : |v| ≤ 1 / 40)
    have hmodel := norm_xiLine_le_model (X := ξ) (u := 2 * t * (horizontalSlope ξ).re)
      (w := v + 2 * t * (horizontalSlope ξ).re) hξ200 (by linarith only [hc1, hc0, hε])
      (by linarith only [hc2, hξ200]) (by linarith only [hc1, hc0, hε, hvb.1])
      (by linarith only [hc2, hξ200, hvb.2])
    rw [add_sub_cancel_right] at hmodel
    have hexp : Real.exp (v * (horizontalSlope ξ).re) * Real.exp (13 * |v|) ≤ Real.exp 4 := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : v * (horizontalSlope ξ).re ≤ |v| * |(horizontalSlope ξ).re| := by
        rw [← abs_mul]
        exact le_abs_self _
      have hα0 : 0 ≤ (horizontalSlope ξ).re := by
        by_contra hn
        have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_le.mp hn).le
        linarith only [this, hc1, hc0, hε]
      rw [abs_of_nonneg hα0, hv] at h1
      rw [hv]
      linarith only [h1, hηα, hη2]
    have hn0 := norm_nonneg (xiLine ξ (2 * t * (horizontalSlope ξ).re))
    have hnorm : ‖xiLine ξ (v + 2 * t * (horizontalSlope ξ).re)‖ ≤
        ‖xiLine ξ (2 * t * (horizontalSlope ξ).re)‖ * Real.exp 4 := by
      refine hmodel.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp hn0
    refine hup.trans ?_
    unfold horizonAmp
    have he := (Real.exp_pos (-(t * (horizontalSlope ξ).re ^ 2))).le
    calc 6 / 5 * (‖xiLine ξ (v + 2 * t * (horizontalSlope ξ).re)‖ * Real.exp (-(t * (horizontalSlope ξ).re ^ 2)))
        ≤ 6 / 5 * ((‖xiLine ξ (2 * t * (horizontalSlope ξ).re)‖ * Real.exp 4) *
            Real.exp (-(t * (horizontalSlope ξ).re ^ 2))) := by gcongr
      _ = _ := by ring
  have hsplit : riemannHeat t ((ξ : ℂ) + I * η) = halfGaussTransform t (xiLine ξ) (-η) +
      starRingEnd ℂ (halfGaussTransform t (xiLine ξ) η) := riemannHeat_eq_halfGaussAverage ht ξ η
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [RCLike.norm_conj]
  have h1 := hbound (-η) (abs_neg η)
  have h2 := hbound η rfl
  linarith only [h1, h2]

/-- **A second zero is far, if the flow is small on a disc.** If `H` vanishes at real points `x < x'` and `|H| ≤ M` on the disc of radius `2R` around `x`, then `x' − x ≥ min(R, |H'(x)| R²/(2M))`: Cauchy's estimate bounds `H″` on the disc of radius `R`. -/
theorem gap_ge_of_disc_bound {H : ℂ → ℂ} (hH : Differentiable ℂ H) {x x' R M : ℝ} (hR : 0 < R) (hM : 0 < M) (hxx' : x < x')
    (hx0 : H (x : ℂ) = 0) (hx'0 : H (x' : ℂ) = 0) (hdisc : ∀ w : ℂ, ‖w - x‖ ≤ 2 * R → ‖H w‖ ≤ M) :
    min R (‖deriv H (x : ℂ)‖ * R ^ 2 / (2 * M)) ≤ x' - x := by
  by_contra hcon
  have hlt := not_le.mp hcon
  set g := x' - x with hgdef
  have hgpos : 0 < g := sub_pos.mpr hxx'
  have hgR : g ≤ R := (hlt.trans_le (min_le_left _ _)).le
  set D₀ := deriv H (x : ℂ) with hD₀
  have hH2 (z : ℂ) (hz : ‖z - x‖ ≤ R) : ‖deriv (deriv H) z‖ ≤ 2 * M / R ^ 2 := by
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR
      (c := z) (C := M) (f := H) hH.diffContOnCl (fun w hw => hdisc w (by
        have h1 := mem_sphere_iff_norm.mp hw
        have h2 := norm_sub_le_norm_sub_add_norm_sub w z (x : ℂ)
        linarith only [h1, h2, hz]))
    have hit : iteratedDeriv 2 H = deriv (deriv H) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [hit] at h
    refine h.trans (le_of_eq ?_)
    norm_num
  have hx'mem : (x' : ℂ) ∈ closedBall (x : ℂ) g := by
    rw [mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hgpos]
  have hxmem : (x : ℂ) ∈ closedBall (x : ℂ) g := mem_closedBall_self hgpos.le
  have hball (z : ℂ) (hz : z ∈ closedBall (x : ℂ) g) : ‖z - x‖ ≤ g := by
    rwa [mem_closedBall, Complex.dist_eq] at hz
  have hdiff2 : Differentiable ℂ (deriv H) := hH.deriv
  have hK : 0 ≤ 2 * M / R ^ 2 := by positivity
  have hDz (z : ℂ) (hz : z ∈ closedBall (x : ℂ) g) : ‖deriv H z - D₀‖ ≤ 2 * M / R ^ 2 * g := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := deriv H)
      (C := 2 * M / R ^ 2) (s := closedBall (x : ℂ) g) (x := (x : ℂ)) (y := z)
      (fun w _ => hdiff2 w) (fun w hw => hH2 w ((hball w hw).trans hgR)) (convex_closedBall _ _) hxmem hz
    exact h.trans (mul_le_mul_of_nonneg_left (hball z hz) hK)
  set h : ℂ → ℂ := fun z => H z - D₀ * (z - x) with hh
  have hhd (z : ℂ) : HasDerivAt h (deriv H z - D₀) z := by
    have h1 := (hH z).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => D₀ * (z - x)) D₀ z := by
      simpa using ((hasDerivAt_id z).sub_const (x : ℂ)).const_mul D₀
    exact h1.sub h2
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := h)
    (C := 2 * M / R ^ 2 * g) (s := closedBall (x : ℂ) g) (x := (x : ℂ)) (y := (x' : ℂ))
    (fun w _ => (hhd w).differentiableAt)
    (fun w hw => by rw [(hhd w).deriv]; exact hDz w hw) (convex_closedBall _ _) hxmem hx'mem
  have hval : h (x' : ℂ) - h (x : ℂ) = -(D₀ * (g : ℝ)) := by
    simp only [hh, hx0, hx'0, hgdef]
    push_cast
    ring
  rw [hval, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos] at hmv
  have hD₀le : ‖D₀‖ ≤ 2 * M / R ^ 2 * g := le_of_mul_le_mul_right hmv hgpos
  have hg2 : ‖D₀‖ * R ^ 2 / (2 * M) ≤ g := by
    rw [div_le_iff₀ (by positivity)]
    calc ‖D₀‖ * R ^ 2 ≤ 2 * M / R ^ 2 * g * R ^ 2 := mul_le_mul_of_nonneg_right hD₀le (by positivity)
      _ = g * (2 * M) := by
        field_simp
  exact absurd hg2 (not_le.mpr (hlt.trans_le (min_le_right _ _)))

/-- **The gaps above the horizon.** Real zeros `x < x'` of `H_t` with `t log(x/2π) ≥ 6600/9991 + ε` and `t log x ≤ 1` satisfy `x' − x ≥ c/α`, `α = ½ log(x/2π)`. -/
theorem exists_gap_ge_above_horizon {ε : ℝ} (hε : 0 < ε) :
    ∃ c X₁ : ℝ, 0 < c ∧ Real.exp 420 ≤ X₁ ∧ ∀ t x x' : ℝ, 0 < t → X₁ ≤ x → t * Real.log x ≤ 1 →
      6600 / 9991 + ε ≤ 2 * t * (horizontalSlope x).re → x < x' →
      riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 → c / (horizontalSlope x).re ≤ x' - x := by
  obtain ⟨δ₀, X₂, hδ₀, hδ₀40, hX₂, hsup⟩ := exists_norm_riemannHeat_le_amp (half_pos hε)
  obtain ⟨X₃, hX₃, hquad⟩ := exists_quadrature_bounds (half_pos hε)
  have h1ε : 0 < 1 / ε := by positivity
  have h1δ : 0 < 1 / δ₀ := by positivity
  have he420 := Real.exp_pos 420
  refine ⟨1 / (20 * Real.exp 26), X₂ + X₃ + Real.exp 420 + 2 * Real.pi * Real.exp (8 / δ₀) + 8 * (1 + 1 / ε),
    by positivity, ?_, ?_⟩
  · have : 0 ≤ 2 * Real.pi * Real.exp (8 / δ₀) := by positivity
    linarith only [hX₂, hX₃, this, h1ε]
  intro t x x' ht hx htL hc hxx' hx0 hx'0
  have hpiE : 0 < 2 * Real.pi * Real.exp (8 / δ₀) := by positivity
  have hxe : Real.exp 420 ≤ x := by linarith only [hx, hX₂, hX₃, hpiE, h1ε]
  have hxpos : 0 < x := by linarith only [hxe, he420]
  have hL420 : 420 ≤ Real.log x := by
    have := Real.log_le_log he420 hxe
    rwa [Real.log_exp] at this
  have ht8 : t ≤ 1 / 8 := by nlinarith only [hL420, htL, ht]
  have hxX₂ : X₂ + 2 ≤ x := by
    have h3 := Real.add_one_le_exp (420 : ℝ)
    linarith only [hx, hX₃, hX₂, hpiE, h1ε, he420, h3]
  have hxX₃ : X₃ + 2 ≤ x := by
    have h3 := Real.add_one_le_exp (420 : ℝ)
    linarith only [hx, hX₃, hX₂, hpiE, h1ε, he420, h3]
  set α := (horizontalSlope x).re with hα
  have hαL : 2 * α ≤ Real.log x := by
    rw [hα, horizontalSlope_re]
    have h1 : x / (2 * Real.pi) ≤ x := div_le_self hxpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hα207 : 207 ≤ α := by
    rw [hα, horizontalSlope_re, Real.log_div hxpos.ne' (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
    have h2 := Real.pi_lt_d2
    linarith only [h1, h2, hL420]
  have hα0 : 0 < α := by linarith only [hα207]
  have hαδ : 4 / δ₀ ≤ α := by
    have h0 : 2 * Real.pi * Real.exp (8 / δ₀) ≤ x := by
      have : 0 ≤ X₂ := by linarith only [hX₂]
      have h3 : 0 ≤ X₃ := by linarith only [hX₃]
      linarith only [hx, this, h3, he420, h1ε]
    have h1 : Real.exp (8 / δ₀) ≤ x / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [h0]
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hα, horizontalSlope_re]
    have h3 : 8 / δ₀ = 2 * (4 / δ₀) := by ring
    linarith only [h2, h3]
  set R := 1 / α with hR
  have hRpos : 0 < R := by positivity
  have hRsmall : R ≤ 1 / 207 := by
    rw [hR]
    exact one_div_le_one_div_of_le (by norm_num) hα207
  have hRδ : 2 * R ≤ δ₀ := by
    rw [hR]
    have h1 : 2 * (1 / α) = 2 / α := by ring
    rw [h1, div_le_iff₀ hα0]
    have h2 := (div_le_iff₀ hδ₀).mp hαδ
    nlinarith only [h2, hδ₀]
  have hαR : α * R = 1 := by
    rw [hR]
    field_simp
  -- nearby heights
  have hc0 : (6600 : ℝ) / 9991 ≥ 3 / 5 := by norm_num
  have hb2 : x ≥ 8 * (1 + 1 / ε) := by
    have : 0 ≤ X₂ := by linarith only [hX₂]
    have h3 : 0 ≤ X₃ := by linarith only [hX₃]
    linarith only [hx, this, h3, he420, hpiE]
  have hnear (ξ : ℝ) (hξ : |ξ - x| ≤ 1) :
      X₂ ≤ ξ ∧ 400 ≤ x ∧ |ξ - x| ≤ x / 2 ∧ 6600 / 9991 + ε / 2 ≤ 2 * t * (horizontalSlope ξ).re ∧
        2 * t * (horizontalSlope ξ).re ≤ 1 ∧ |(horizontalSlope ξ).re - α| ≤ 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hξ
    have hx400 : (400 : ℝ) ≤ x := by
      have h3 := Real.add_one_le_exp (420 : ℝ)
      linarith only [hxe, h3]
    have hξpos : 0 < ξ := by linarith only [h1, hx400]
    have hmin : x / 2 ≤ min ξ x := le_min (by linarith only [h1, hx400]) (by linarith only [hxpos])
    have hminpos : 0 < min ξ x := lt_of_lt_of_le (by positivity) hmin
    have hslope : |(horizontalSlope ξ).re - α| ≤ 2 / x := by
      have h3 := abs_horizontalSlope_re_sub_le hxpos hξpos
      rw [min_comm] at h3
      refine h3.trans ?_
      rw [div_le_div_iff₀ hminpos hxpos]
      have h4 : |ξ - x| * x ≤ 1 * x := mul_le_mul_of_nonneg_right hξ hxpos.le
      linarith only [h4, hmin]
    have hs1 : 2 / x ≤ 1 := by
      rw [div_le_one hxpos]
      linarith only [hx400]
    have hs2 : 2 / x ≤ ε := by
      rw [div_le_iff₀ hxpos]
      have h5 : 8 * (1 / ε) ≤ x := by linarith only [hb2, hxpos]
      have h6 : ε * (8 * (1 / ε)) = 8 := by field_simp
      have h7 := mul_le_mul_of_nonneg_left h5 hε.le
      linarith only [h6, h7]
    refine ⟨by linarith only [hxX₂, h1], hx400, by linarith only [hξ, hx400], ?_, ?_, hslope.trans hs1⟩
    · have h8 := (abs_le.mp (hslope.trans hs2)).1
      have h9 : 2 * t * (-ε) ≤ 2 * t * ((horizontalSlope ξ).re - α) :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      have h10 : 2 * t * ε ≤ ε / 2 := by nlinarith only [ht8, hε, ht]
      nlinarith only [h9, h10, hc]
    · rw [horizontalSlope_re]
      have h11 : ξ / (2 * Real.pi) ≤ x := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [h2, hx400, Real.pi_gt_three]
      have h12 := Real.log_le_log (by positivity) h11
      have h13 := mul_le_mul_of_nonneg_left h12 ht.le
      linarith only [h13, htL]
  set P := horizonAmp t x with hP
  have hP0 : 0 < P := by
    unfold horizonAmp at hP
    rw [hP]
    refine mul_pos (norm_pos_iff.mpr ?_) (Real.exp_pos _)
    unfold xiLine
    rw [xiLine_point]
    refine xi_ne_zero_of_one_lt_re ?_
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero]
    rw [← hα]
    linarith only [hc, hc0, hε]
  set M := 12 / 5 * Real.exp 26 * P with hM
  have hMpos : 0 < M := by positivity
  have hRone : 2 * R ≤ 1 := by linarith only [hRsmall]
  have hcα : 2 * t * α ≤ 1 := by nlinarith only [hαL, htL, ht]
  -- the flow on the double disc
  have hdisc (w : ℂ) (hw : ‖w - x‖ ≤ 2 * R) : ‖riemannHeat t w‖ ≤ M := by
    have hre : |w.re - x| ≤ 2 * R := by
      have h := Complex.abs_re_le_norm (w - x)
      rw [Complex.sub_re, Complex.ofReal_re] at h
      exact h.trans hw
    have him : |w.im| ≤ 2 * R := by
      have h := Complex.abs_im_le_norm (w - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
      exact h.trans hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnear w.re (hre.trans hRone)
    have hαξ : (horizontalSlope w.re).re ≤ α + 1 := by
      have := (abs_le.mp h6).2
      linarith only [this]
    have hηα : |w.im| * (horizontalSlope w.re).re ≤ 3 := by
      have h7 : |w.im| * (horizontalSlope w.re).re ≤ 2 * R * (α + 1) :=
        mul_le_mul him hαξ (by
          have hc' : 0 < 2 * t * (horizontalSlope w.re).re := by linarith only [h4, hc0, hε]
          by_contra hn
          have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_le.mp hn).le
          linarith only [this, hc']) (by positivity)
      have h8 : 2 * R * (α + 1) = 2 * (α * R) + 2 * R := by ring
      rw [h8, hαR] at h7
      linarith only [h7, hRone]
    have hb := hsup t w.re w.im ht ht8 h1 h4 h5 (him.trans hRδ) hηα
    have hw' : (w.re : ℂ) + I * (w.im : ℂ) = w := by
      apply Complex.ext <;> simp
    rw [hw'] at hb
    have hamp := horizonAmp_height_le (x := x) (y := w.re) ht ht8 h2 h3
      (by rw [← hα]; linarith only [hc, hc0, hε]) (by rw [← hα]; exact hcα)
      (by linarith only [h4, hc0, hε]) h5
    rw [← hP] at hamp
    have hexp : Real.exp (22 * |w.re - x|) ≤ Real.exp 22 :=
      Real.exp_le_exp.mpr (by linarith only [hre, hRone])
    have hamp2 : horizonAmp t w.re ≤ P * Real.exp 22 :=
      hamp.trans (mul_le_mul_of_nonneg_left hexp hP0.le)
    refine hb.trans ?_
    calc 12 / 5 * Real.exp 4 * horizonAmp t w.re
        ≤ 12 / 5 * Real.exp 4 * (P * Real.exp 22) := mul_le_mul_of_nonneg_left hamp2 (by positivity)
      _ = M := by
        rw [hM, show (26 : ℝ) = 4 + 22 by norm_num, Real.exp_add]
        ring
  have hdiff := differentiable_riemannHeat ht.le
  have hmin := gap_ge_of_disc_bound hdiff hRpos hMpos hxx' hx0 hx'0 hdisc
  -- the quadrature bound at the zero
  have hq := (hquad t x ht ht8 (by linarith only [hxX₃]) (by rw [← hα]; linarith only [hc, hε]) (by rw [← hα]; exact hcα)).2
  rw [← hP, ← hα, hx0, norm_zero] at hq
  set D₀ := deriv (riemannHeat t) (x : ℂ) with hD₀
  have hq2 : (α * P) ^ 2 ≤ (2 * ‖D₀‖) ^ 2 := by
    have h1 : P ^ 2 * α ^ 2 ≤ 4 * ‖D₀‖ ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ α ^ 2)
      refine h2.trans (le_of_eq ?_)
      field_simp
      ring
    nlinarith only [h1]
  have hq3 : α * P ≤ 2 * ‖D₀‖ := (sq_le_sq₀ (by positivity) (by positivity)).mp hq2
  have hE1 : 1 ≤ Real.exp 26 := Real.one_le_exp (by norm_num)
  have hEpos := Real.exp_pos 26
  have hcoef : 1 / (20 * Real.exp 26) / α ≤ min R (‖D₀‖ * R ^ 2 / (2 * M)) := by
    refine le_min ?_ ?_
    · rw [hR]
      refine div_le_div_of_nonneg_right ?_ hα0.le
      rw [div_le_one (by positivity)]
      linarith only [hE1]
    · have h1 : ‖D₀‖ * R ^ 2 / (2 * M) = ‖D₀‖ / (α ^ 2 * (2 * M)) := by
        rw [hR]
        field_simp
      rw [h1, div_le_div_iff₀ hα0 (by positivity), hM]
      have hval : 1 / (20 * Real.exp 26) * (α ^ 2 * (2 * (12 / 5 * Real.exp 26 * P))) = 6 / 25 * (α * (α * P)) := by
        field_simp
        ring
      rw [hval]
      have h2 := mul_le_mul_of_nonneg_left hq3 hα0.le
      have h3 : 0 < α * (α * P) := by positivity
      nlinarith only [h2, h3]
  exact hcoef.trans hmin

/-- **The central inequality above the horizon.** In the zone `6600/9991 + ε ≤ t log(x/2π)`, `t log x ≤ 1`, the gaps of the real zeros satisfy `(x' − x)² ≥ c min(t, log⁻²(2 + |x|))`. -/
theorem exists_central_inequality_above_horizon {ε : ℝ} (hε : 0 < ε) :
    ∃ c X₁ : ℝ, 0 < c ∧ Real.exp 420 ≤ X₁ ∧ ∀ t x x' : ℝ, 0 < t → X₁ ≤ x → t * Real.log x ≤ 1 →
      6600 / 9991 + ε ≤ 2 * t * (horizontalSlope x).re → x < x' →
      riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
      c * min t (1 / Real.log (2 + |x|) ^ 2) ≤ (x' - x) ^ 2 := by
  obtain ⟨c, X₁, hc, hX₁, hgap⟩ := exists_gap_ge_above_horizon hε
  refine ⟨4 * c ^ 2, X₁, by positivity, hX₁, ?_⟩
  intro t x x' ht hx htL hcc hxx' hx0 hx'0
  have hxe : Real.exp 420 ≤ x := hX₁.trans hx
  have he420 := Real.exp_pos 420
  have hxpos : 0 < x := by linarith only [hxe, he420]
  have hL : 420 ≤ Real.log x := by
    have := Real.log_le_log he420 hxe
    rwa [Real.log_exp] at this
  have hL2 : Real.log x ≤ Real.log (2 + |x|) := by
    apply Real.log_le_log hxpos
    have := le_abs_self x
    linarith only [this]
  have hLpos : 0 < Real.log (2 + |x|) := by linarith only [hL, hL2]
  have hg := hgap t x x' ht hx htL hcc hxx' hx0 hx'0
  have hαL : 2 * (horizontalSlope x).re ≤ Real.log x := by
    rw [horizontalSlope_re]
    have h1 : x / (2 * Real.pi) ≤ x := div_le_self hxpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hαpos : 0 < (horizontalSlope x).re := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_lt.mp hn)
    have hc0 : (6600 : ℝ) / 9991 ≥ 3 / 5 := by norm_num
    linarith only [this, hcc, hε, hc0]
  have hg2 : 2 * c / Real.log (2 + |x|) ≤ x' - x := by
    refine le_trans ?_ hg
    rw [div_le_div_iff₀ hLpos hαpos]
    have := mul_le_mul_of_nonneg_left (hαL.trans hL2) hc.le
    linarith only [this]
  have hsq : (2 * c / Real.log (2 + |x|)) ^ 2 ≤ (x' - x) ^ 2 := pow_le_pow_left₀ (by positivity) hg2 2
  refine le_trans ?_ hsq
  have hmin : min t (1 / Real.log (2 + |x|) ^ 2) ≤ 1 / Real.log (2 + |x|) ^ 2 := min_le_right _ _
  refine (mul_le_mul_of_nonneg_left hmin (by positivity)).trans (le_of_eq ?_)
  field_simp
  norm_num

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
