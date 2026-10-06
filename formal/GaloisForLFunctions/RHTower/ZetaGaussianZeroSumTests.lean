import GaloisForLFunctions.RHTower.ZetaGaussianZeroSums

/-!
# The three Gaussian zero sums

Over the zeros `ρ` of `ζ` in `[−½, 11/10] × [t₀, Y]` (`t₀` the fixed bottom height, `Y` admissible,
`Y ≈ T²`), with `G(s) = r^s g_T(s)`, `r > 0`:

* (`exists_abs_re_zeroSum_gW_le`) Landau–Gonek: `Re Σ m_ρ G(ρ) = O(T log T)`;
* (`exists_abs_re_zeroSum_zetaChi_gW_le`) `Re Σ m_ρ χ(ρ) G(ρ) = O(T)`;
* (`exists_abs_re_zeroSum_deriv_gW_sub_le`) Rule A, kernel form:
  `Re Σ m_ρ ζ'(ρ) G(ρ) = (r/2) Σ_n ℓ(n) J_T(nr) + O(T)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

theorem continuous_ofReal_cpow {r : ℝ} (hr : 0 < r) : Continuous fun s : ℂ => (r : ℂ) ^ s :=
  continuous_id.const_cpow (Or.inl (by exact_mod_cast hr.ne'))

theorem differentiable_ofReal_cpow {r : ℝ} (hr : 0 < r) : Differentiable ℂ fun s : ℂ => (r : ℂ) ^ s :=
  differentiable_id.const_cpow (Or.inl (by exact_mod_cast hr.ne'))

theorem norm_ofReal_cpow_rightPt {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ‖(r : ℂ) ^ (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ = r ^ (11 / 10 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp

/-! ## Landau–Gonek -/

theorem exists_abs_re_zeroSum_gW_le {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * ((r : ℂ) ^ w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1) := by
  obtain ⟨CLG, hCLG0, hCLG⟩ := exists_leftLine_logDeriv hr
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bottom_edge_le (h := fun s => (r : ℂ) ^ s) (t₀ := bottomHeight)
    (continuousOn_bottom fun _ => (continuous_ofReal_cpow hr).continuousAt)
  obtain ⟨Ml, hMl0, hMl⟩ := exists_left_piece_le (h := fun s => (r : ℂ) ^ s)
    (zero_le_one.trans one_le_bottomHeight)
    (continuousOn_leftPiece (fun y => (continuous_ofReal_cpow hr).continuousAt) _)
  obtain ⟨KR, hKR0, hKR⟩ := exists_norm_logDeriv_rightEdge_le
  obtain ⟨CL, hCL0, hCL⟩ := exists_norm_logDeriv_leftPt_le
  have hCh : 0 ≤ r ^ (-1 / 2 : ℝ) + r ^ (11 / 10 : ℝ) := by positivity
  have hCL' : 0 ≤ r ^ (-1 / 2 : ℝ) * CL := by positivity
  have hA := edgeConst_nonneg 0 1 hMb0 hMl0 hCh hCL'
  have hB : 0 ≤ r ^ (11 / 10 : ℝ) * KR * Real.exp 1 * Real.sqrt Real.pi := by positivity
  refine ⟨(edgeConst Mb Ml (r ^ (-1 / 2 : ℝ) + r ^ (11 / 10 : ℝ)) (r ^ (-1 / 2 : ℝ) * CL) 0 1 +
    r ^ (11 / 10 : ℝ) * KR * Real.exp 1 * Real.sqrt Real.pi) / (2 * Real.pi) + CLG / (4 * Real.pi),
    add_nonneg (div_nonneg (add_nonneg hA hB) (by positivity)) (by positivity),
    fun T hT Y hY => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  obtain ⟨hint, hLG⟩ := hCLG T hT1
  have hedges := abs_re_zeroSum_add_le_edges (h := fun s => (r : ℂ) ^ s) (k := 0) (N := 1)
    ((differentiable_ofReal_cpow hr).differentiableOn.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im))
    hCh (by positivity : (0 : ℝ) ≤ r ^ (11 / 10 : ℝ)) hKR0 hCL' hMb hMl
    (fun Y _ x hx => by
      rw [pow_zero, mul_one]
      exact norm_ofReal_cpow_le hr (by simp; linarith [hx.1]) (by simp; linarith [hx.2]))
    (fun y => (norm_ofReal_cpow_rightPt hr y).le)
    ((continuous_ofReal_cpow hr).comp (by fun_prop)) hKR
    (fun y => by
      rw [norm_mul, norm_cpow_leftPt hr]
      have := hCL y
      calc r ^ (-1 / 2 : ℝ) * ‖deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)‖
          ≤ r ^ (-1 / 2 : ℝ) * (CL * (1 + |y|) ^ 1) := by gcongr
        _ = _ := by ring)
    hT hY
    (hint.congr (Eventually.of_forall fun y => by simp only [logDeriv_apply, gW]; ring))
    (fun y => by
      rw [leftPt_neg, logDeriv_quot_conj, ofReal_cpow_conj hr, gaussWeight_conj, ← map_mul, ← map_mul])
  have hq : |(1 / (4 * Real.pi)) * (∫ y : ℝ, ((r : ℂ) ^ leftPt y * gaussWeight T (leftPt y)) *
      (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))).re| ≤
      CLG / (4 * Real.pi) * T * (Real.log T + 1) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hle : ‖∫ y : ℝ, ((r : ℂ) ^ leftPt y * gaussWeight T (leftPt y)) *
        (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤ CLG * T * (Real.log T + 1) := by
      refine (norm_integral_le_integral_norm _).trans (le_trans (le_of_eq ?_) hLG)
      congr 1; funext y; simp only [logDeriv_apply, gW]; ring_nf
    calc 1 / (4 * Real.pi) * |(∫ y : ℝ, ((r : ℂ) ^ leftPt y * gaussWeight T (leftPt y)) *
          (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))).re|
        ≤ 1 / (4 * Real.pi) * (CLG * T * (Real.log T + 1)) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hle) (by positivity)
      _ = _ := by ring
  have hL : 1 ≤ Real.log T + 1 := by have := Real.log_nonneg hT1; linarith
  exact abs_le_of_edge_bound hA hB hT1 hL hedges hq

/-! ## The `χ`-twisted sum -/

theorem zetaChi_analyticAt_of_im_ne {z : ℂ} (hz : z.im ≠ 0) : AnalyticAt ℂ zetaChi z := by
  refine zetaChi_analyticAt fun h => hz ?_
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have := congrArg Complex.im hn
  simpa using this

theorem zetaChi_analyticAt_rightPt (y : ℝ) :
    AnalyticAt ℂ zetaChi (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) := by
  refine zetaChi_analyticAt fun h => ?_
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have h1 := congrArg Complex.re hn
  simp only [sub_re, one_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, neg_re,
    natCast_re, natCast_im, mul_zero, mul_one, sub_zero, zero_mul, re_ofNat, im_ofNat] at h1
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; norm_num at h1
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
    linarith

/-- `|χ(x + iY)| ≤ C (1 + Y)` for `x ∈ [−½, 11/10]`, `Y ≥ 2`. -/
theorem exists_norm_zetaChi_top_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 2 ≤ Y → ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10),
      ‖zetaChi ((x : ℂ) + Y * I)‖ ≤ C * (1 + Y) ^ 1 := by
  obtain ⟨CA, hCA, hA⟩ := exists_norm_zetaChi_le_of_two_le_abs
  refine ⟨Real.exp 2 + CA, by positivity, fun Y hY x hx => ?_⟩
  have hYa : |Y| = Y := abs_of_pos (by linarith)
  have hY1 : (1 : ℝ) ≤ 1 + Y := by linarith
  rw [pow_one]
  rcases le_total x (1 / 2) with h | h
  · have := norm_zetaChi_le_half_strip (σ := x) (t := Y) hx.1 h (by rw [hYa]; exact hY)
    rw [hYa] at this
    nlinarith [Real.exp_pos 2]
  · have := hA x Y h (by linarith [hx.2]) (by rw [hYa]; exact hY)
    rw [hYa] at this
    have hp : (1 + Y) ^ (-(x - 1 / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
    have : ‖zetaChi ((x : ℂ) + Y * I)‖ ≤ CA := this.trans (mul_le_of_le_one_right hCA hp)
    nlinarith [Real.exp_pos 2]

/-- `|χ(11/10 + iy)| ≤ C`. -/
theorem exists_norm_zetaChi_rightPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖zetaChi (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hR⟩ := exists_norm_zetaChi_le_rightOfOne
  refine ⟨C, hC, fun y => (hR (11 / 10) y le_rfl (by norm_num)).trans ?_⟩
  exact mul_le_of_le_one_right hC
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg y]) (by norm_num))

/-- **The `χ`-twisted Gaussian zero sum**: `Re Σ m_ρ χ(ρ) r^ρ g_T(ρ) = O(T)`. -/
theorem exists_abs_re_zeroSum_zetaChi_gW_le {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → r ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y,
          (mult w : ℂ) * (zetaChi w * (r : ℂ) ^ w * gaussWeight T w)).re| ≤ C * T := by
  obtain ⟨CCT, hCCT0, hCCT⟩ := exists_leftLine_zetaChi_logDeriv hr
  have hcont : ∀ z : ℂ, z.im ≠ 0 → ContinuousAt (fun s => zetaChi s * (r : ℂ) ^ s) z := fun z hz =>
    (zetaChi_analyticAt_of_im_ne hz).continuousAt.mul (continuous_ofReal_cpow hr).continuousAt
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bottom_edge_le (h := fun s => zetaChi s * (r : ℂ) ^ s)
    (t₀ := bottomHeight) (continuousOn_bottom fun x => hcont _ (by
      simp; linarith [one_le_bottomHeight]))
  obtain ⟨Ml, hMl0, hMl⟩ := exists_left_piece_le (h := fun s => zetaChi s * (r : ℂ) ^ s)
    (zero_le_one.trans one_le_bottomHeight)
    (continuousOn_leftPiece (fun y => (continuousAt_zetaChi_of_mem_leftStrip
      (leftPt_mem_leftStrip y)).mul (continuous_ofReal_cpow hr).continuousAt) _)
  obtain ⟨KR, hKR0, hKR⟩ := exists_norm_logDeriv_rightEdge_le
  obtain ⟨CQ, hCQ0, hCQ⟩ := exists_norm_logDeriv_leftPt_le
  obtain ⟨Cχt, hCχt0, hCχt⟩ := exists_norm_zetaChi_top_le
  obtain ⟨Cχr, hCχr0, hCχr⟩ := exists_norm_zetaChi_rightPt_le
  obtain ⟨Cχl, hCχl0, hCχl⟩ := exists_norm_zetaChi_leftPt_le
  set P : ℝ := r ^ (-1 / 2 : ℝ) + r ^ (11 / 10 : ℝ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hCh : 0 ≤ Cχt * P := mul_nonneg hCχt0 hP0
  have hCR : 0 ≤ Cχr * r ^ (11 / 10 : ℝ) := by positivity
  have hCL : 0 ≤ r ^ (-1 / 2 : ℝ) * Cχl * CQ := by positivity
  have hA := edgeConst_nonneg 1 2 hMb0 hMl0 hCh hCL
  have hB : 0 ≤ Cχr * r ^ (11 / 10 : ℝ) * KR * Real.exp 1 * Real.sqrt Real.pi := by positivity
  refine ⟨((edgeConst Mb Ml (Cχt * P) (r ^ (-1 / 2 : ℝ) * Cχl * CQ) 1 2 +
    Cχr * r ^ (11 / 10 : ℝ) * KR * Real.exp 1 * Real.sqrt Real.pi) / (2 * Real.pi) +
      CCT / (4 * Real.pi)) * 1,
    mul_nonneg (add_nonneg (div_nonneg (add_nonneg hA hB) (by positivity)) (by positivity))
      zero_le_one, fun T hT hrT Y hY => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  obtain ⟨hint, hCT⟩ := hCCT T hT1 ((one_le_div (hr)).mpr hrT)
  have hedges := abs_re_zeroSum_add_le_edges (h := fun s => zetaChi s * (r : ℂ) ^ s) (k := 1) (N := 2)
    (fun s hs => (zetaChi_analyticAt_of_im_ne (ne_of_gt hs)).mul
      ((differentiable_ofReal_cpow hr).analyticAt s))
    hCh hCR hKR0 hCL hMb hMl
    (fun Y hY x hx => by
      rw [norm_mul]
      have h1 := hCχt Y hY x hx
      have h2 := norm_ofReal_cpow_le hr (s := (x : ℂ) + Y * I) (by simp; linarith [hx.1])
        (by simp; linarith [hx.2])
      calc ‖zetaChi ((x : ℂ) + Y * I)‖ * ‖(r : ℂ) ^ ((x : ℂ) + Y * I)‖
          ≤ (Cχt * (1 + Y) ^ 1) * P := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = Cχt * P * (1 + Y) ^ 1 := by ring)
    (fun y => by
      rw [norm_mul, norm_ofReal_cpow_rightPt hr]
      exact mul_le_mul_of_nonneg_right (hCχr y) (by positivity))
    (continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (g := fun s => zetaChi s * (r : ℂ) ^ s)
        (f := fun y : ℝ => ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)
        ((zetaChi_analyticAt_rightPt y).continuousAt.mul (continuous_ofReal_cpow hr).continuousAt)
        (by fun_prop : Continuous fun y : ℝ => ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).continuousAt)
    hKR
    (fun y => by
      rw [norm_mul, norm_mul, norm_cpow_leftPt hr]
      have h1 := hCχl y
      have h2 := hCQ y
      calc ‖zetaChi (leftPt y)‖ * r ^ (-1 / 2 : ℝ) *
            ‖deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)‖
          ≤ (Cχl * (1 + |y|) ^ 1) * r ^ (-1 / 2 : ℝ) * (CQ * (1 + |y|) ^ 1) := by gcongr
        _ = r ^ (-1 / 2 : ℝ) * Cχl * CQ * (1 + |y|) ^ 2 := by ring)
    hT hY
    (hint.congr (Eventually.of_forall fun y => by simp only [logDeriv_apply, gW]; ring))
    (fun y => by
      rw [leftPt_neg, logDeriv_quot_conj, zetaChi_conj, ofReal_cpow_conj hr, gaussWeight_conj,
        ← map_mul, ← map_mul, ← map_mul])
  have hq : |(1 / (4 * Real.pi)) * (∫ y : ℝ, (zetaChi (leftPt y) * (r : ℂ) ^ leftPt y *
      gaussWeight T (leftPt y)) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))).re| ≤
      CCT / (4 * Real.pi) * T * 1 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hle : ‖∫ y : ℝ, (zetaChi (leftPt y) * (r : ℂ) ^ leftPt y * gaussWeight T (leftPt y)) *
        (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤ CCT * T := by
      refine le_trans (le_of_eq ?_) hCT
      congr 2; funext y; simp only [logDeriv_apply, gW]; ring
    calc 1 / (4 * Real.pi) * |(∫ y : ℝ, (zetaChi (leftPt y) * (r : ℂ) ^ leftPt y *
          gaussWeight T (leftPt y)) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))).re|
        ≤ 1 / (4 * Real.pi) * (CCT * T) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hle) (by positivity)
      _ = _ := by ring
  have h := abs_le_of_edge_bound hA hB hT1 le_rfl hedges hq
  calc _ ≤ _ := h
    _ = _ := by ring

/-! ## Rule A -/

/-- `|ζ'(11/10 + iy)| ≤ C`. -/
theorem exists_norm_deriv_riemannZeta_rightPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_logDeriv_rightEdge_le
  set Z : ℝ := ∑' n, ‖LSeries.term (1 : ℕ → ℂ) ((11 / 10 : ℝ) : ℂ) n‖
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨K * Z, mul_nonneg hK0 hZ0, fun y => ?_⟩
  have hre : (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).re = 11 / 10 := by simp
  have h1 : 1 < (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).re := by rw [hre]; norm_num
  have hζ : ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ Z := by
    rw [← LSeries_one_eq_riemannZeta h1]
    exact norm_LSeries_le_of_re hre (LSeriesSummable_one_iff.mpr (by simp; norm_num))
  rw [← div_mul_cancel₀ (deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I))
    (riemannZeta_ne_zero_of_one_lt_re h1), norm_mul]
  exact mul_le_mul (hK y) hζ (norm_nonneg _) hK0

theorem integrable_sq_logDeriv_gW {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ T : ℝ, 1 ≤ T →
      Integrable (fun y : ℝ => (deriv riemannZeta (leftPt y) * (r : ℂ) ^ leftPt y *
        gaussWeight T (leftPt y)) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))) := by
  obtain ⟨Cd, Nd, hCd0, hCd⟩ := exists_norm_deriv_riemannZeta_leftPt_le
  obtain ⟨CQ, hCQ0, hCQ⟩ := exists_norm_logDeriv_leftPt_le
  refine ⟨r ^ (-1 / 2 : ℝ) * Cd * CQ, Nd + 1, fun T hT => ?_⟩
  refine integrable_of_poly_gauss (C := r ^ (-1 / 2 : ℝ) * Cd * CQ) (N := Nd + 1) ?_ hT fun y => ?_
  · exact ((continuous_deriv_riemannZeta_leftPt.mul ((continuous_ofReal_cpow hr).comp
      continuous_leftPt)).mul ((differentiable_gaussWeight T).continuous.comp continuous_leftPt)).mul
      continuous_logDeriv_quot_leftPt
  · rw [norm_mul, norm_mul, norm_mul, norm_cpow_leftPt hr, norm_gaussWeight_leftPt]
    have h1 := hCd y
    have h2 := hCQ y
    calc ‖deriv riemannZeta (leftPt y)‖ * r ^ (-1 / 2 : ℝ) * Real.exp ((1 - y ^ 2) / T ^ 2) *
          ‖deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)‖
        ≤ (Cd * (1 + |y|) ^ Nd) * r ^ (-1 / 2 : ℝ) * Real.exp ((1 - y ^ 2) / T ^ 2) *
          (CQ * (1 + |y|) ^ 1) := by gcongr
      _ = r ^ (-1 / 2 : ℝ) * Cd * CQ * (1 + |y|) ^ (Nd + 1) * Real.exp ((1 - y ^ 2) / T ^ 2) := by
          ring

/-- **Rule A, kernel form**: `Re Σ m_ρ ζ'(ρ) r^ρ g_T(ρ) = (r/2) Σ_n ℓ(n) J_T(nr) + O(T)`. -/
theorem exists_abs_re_zeroSum_deriv_gW_sub_le {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → r ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y,
          (mult w : ℂ) * (deriv riemannZeta w * (r : ℂ) ^ w * gaussWeight T w)).re -
        r / 2 * ∑' n : ℕ, (if n = 0 then 0 else logVM n * leftKernel T (n * r))| ≤ C * T := by
  obtain ⟨CRA, hCRA0, hCRA⟩ := exists_leftLine_sq_logDeriv hr
  obtain ⟨_, _, hintg⟩ := integrable_sq_logDeriv_gW hr
  have hcont : ∀ z : ℂ, z ≠ 1 → ContinuousAt (fun s => deriv riemannZeta s * (r : ℂ) ^ s) z :=
    fun z hz => (continuousAt_deriv_riemannZeta_of_ne hz).mul
      (continuous_ofReal_cpow hr).continuousAt
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bottom_edge_le (h := fun s => deriv riemannZeta s * (r : ℂ) ^ s)
    (t₀ := bottomHeight) (continuousOn_bottom fun x => hcont _ (bottomPt_ne_one x))
  obtain ⟨Ml, hMl0, hMl⟩ := exists_left_piece_le (h := fun s => deriv riemannZeta s * (r : ℂ) ^ s)
    (zero_le_one.trans one_le_bottomHeight)
    (continuousOn_leftPiece (fun y => hcont _ (leftPt_ne_one y)) _)
  obtain ⟨KR, hKR0, hKR⟩ := exists_norm_logDeriv_rightEdge_le
  obtain ⟨CQ, hCQ0, hCQ⟩ := exists_norm_logDeriv_leftPt_le
  obtain ⟨Cdt, Nt, hCdt0, hCdt⟩ := RHTower.exists_bound_norm_deriv_riemannZeta_strip 2
  obtain ⟨Cdr, hCdr0, hCdr⟩ := exists_norm_deriv_riemannZeta_rightPt_le
  obtain ⟨Cdl, Nl, hCdl0, hCdl⟩ := exists_norm_deriv_riemannZeta_leftPt_le
  set P : ℝ := r ^ (-1 / 2 : ℝ) + r ^ (11 / 10 : ℝ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hCh : 0 ≤ Cdt * 2 ^ Nt * P := by positivity
  have hCR : 0 ≤ Cdr * r ^ (11 / 10 : ℝ) := by positivity
  have hCL : 0 ≤ r ^ (-1 / 2 : ℝ) * Cdl * CQ := by positivity
  have hA := edgeConst_nonneg Nt (Nl + 1) hMb0 hMl0 hCh hCL
  have hB : 0 ≤ Cdr * r ^ (11 / 10 : ℝ) * KR * Real.exp 1 * Real.sqrt Real.pi := by positivity
  refine ⟨((edgeConst Mb Ml (Cdt * 2 ^ Nt * P) (r ^ (-1 / 2 : ℝ) * Cdl * CQ) Nt (Nl + 1) +
    Cdr * r ^ (11 / 10 : ℝ) * KR * Real.exp 1 * Real.sqrt Real.pi) / (2 * Real.pi) +
      CRA / (4 * Real.pi)) * 1,
    mul_nonneg (add_nonneg (div_nonneg (add_nonneg hA hB) (by positivity)) (by positivity))
      zero_le_one, fun T hT hrT Y hY => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hRA := hCRA T hT1 ((one_le_div hr).mpr hrT)
  have hedges := abs_re_zeroSum_add_le_edges (h := fun s => deriv riemannZeta s * (r : ℂ) ^ s)
    (k := Nt) (N := Nl + 1)
    (fun s hs => (analyticAt_riemannZeta_of_ne_one (ne_one_of_im_pos hs)).deriv.mul
      ((differentiable_ofReal_cpow hr).analyticAt s))
    hCh hCR hKR0 hCL hMb hMl
    (fun Y hY x hx => by
      rw [norm_mul]
      have hYa : |Y| = Y := abs_of_pos (by linarith)
      have h1 := hCdt ((x : ℂ) + Y * I) (by simp; rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
        (by simp [hYa]; exact hY)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero,
        zero_add, hYa] at h1
      have h2 := norm_ofReal_cpow_le hr (s := (x : ℂ) + Y * I) (by simp; linarith [hx.1])
        (by simp; linarith [hx.2])
      have h3 : (2 * Y) ^ Nt ≤ 2 ^ Nt * (1 + Y) ^ Nt := by
        rw [← mul_pow]; gcongr; linarith
      calc ‖deriv riemannZeta ((x : ℂ) + Y * I)‖ * ‖(r : ℂ) ^ ((x : ℂ) + Y * I)‖
          ≤ (Cdt * (2 ^ Nt * (1 + Y) ^ Nt)) * P :=
            mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h3 hCdt0)) h2 (norm_nonneg _)
              (by positivity)
        _ = Cdt * 2 ^ Nt * P * (1 + Y) ^ Nt := by ring)
    (fun y => by
      rw [norm_mul, norm_ofReal_cpow_rightPt hr]
      exact mul_le_mul_of_nonneg_right (hCdr y) (by positivity))
    (continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (g := fun s => deriv riemannZeta s * (r : ℂ) ^ s)
        (f := fun y : ℝ => ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) (hcont _ (rightPt_ne_one y))
        (by fun_prop : Continuous fun y : ℝ => ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).continuousAt)
    hKR
    (fun y => by
      rw [norm_mul, norm_mul, norm_cpow_leftPt hr]
      have h1 := hCdl y
      have h2 := hCQ y
      calc ‖deriv riemannZeta (leftPt y)‖ * r ^ (-1 / 2 : ℝ) *
            ‖deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)‖
          ≤ (Cdl * (1 + |y|) ^ Nl) * r ^ (-1 / 2 : ℝ) * (CQ * (1 + |y|) ^ 1) := by gcongr
        _ = r ^ (-1 / 2 : ℝ) * Cdl * CQ * (1 + |y|) ^ (Nl + 1) := by ring)
    hT hY (hintg T hT1)
    (fun y => by
      rw [leftPt_neg, logDeriv_quot_conj, deriv_riemannZeta_conj_eq, ofReal_cpow_conj hr,
        gaussWeight_conj, ← map_mul, ← map_mul, ← map_mul])
  set S : ℝ := ∑' n : ℕ, (if n = 0 then 0 else logVM n * leftKernel T (n * r)) with hS
  set F : ℂ := ∫ y : ℝ, (deriv riemannZeta (leftPt y) * (r : ℂ) ^ leftPt y *
      gaussWeight T (leftPt y)) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)) with hF
  have hSc : (∑' n : ℕ, (if n = 0 then (0 : ℂ) else (logVM n : ℂ) * leftKernel T (n * r))) =
      (S : ℂ) := by
    rw [hS, Complex.ofReal_tsum]
    congr 1; funext n; split_ifs <;> push_cast <;> rfl
  have hFeq : (∫ t : ℝ, deriv riemannZeta (leftPt t) ^ 2 / riemannZeta (leftPt t) *
      gW T r (leftPt t)) = F := by
    rw [hF]; congr 1; funext y; simp only [gW]; ring
  rw [hFeq, hSc] at hRA
  set E : ℂ := F + 2 * Real.pi * r * (S : ℂ) with hE
  have hER : E.re = F.re + 2 * Real.pi * r * S := by
    rw [hE, Complex.add_re]
    congr 1
    rw [show (2 : ℂ) * (Real.pi : ℂ) * (r : ℂ) * (S : ℂ) = ((2 * Real.pi * r * S : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  have hq : |(1 / (4 * Real.pi)) * E.re| ≤ CRA / (4 * Real.pi) * T * 1 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (4 * Real.pi) * |E.re| ≤ 1 / (4 * Real.pi) * (CRA * T) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hRA) (by positivity)
      _ = _ := by ring
  have hsum : (∑ w ∈ rectZeros bottomHeight Y,
        (mult w : ℂ) * (deriv riemannZeta w * (r : ℂ) ^ w * gaussWeight T w)).re - r / 2 * S +
      (1 / (4 * Real.pi)) * E.re =
      (∑ w ∈ rectZeros bottomHeight Y,
        (mult w : ℂ) * (deriv riemannZeta w * (r : ℂ) ^ w * gaussWeight T w)).re +
      (1 / (4 * Real.pi)) * F.re := by
    rw [hER]; field_simp; ring
  rw [← hsum] at hedges
  have h := abs_le_of_edge_bound hA hB hT1 le_rfl hedges hq
  calc _ ≤ _ := h
    _ = _ := by ring

end

end RHTower.GaussZeroSum
