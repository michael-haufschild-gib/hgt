import GaloisForLFunctions.RHTower.ZetaLeftLineIdentities
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# Growth on the line `Re s = −½`

For `s = −½ + it`, with constants independent of `t`:

* `|χ(s)| ≤ C(1 + |t|)`, `|ζ(s)| ≤ C(1 + |t|)` (`exists_norm_zetaChi_leftPt_le`,
  `exists_norm_riemannZeta_leftPt_le`);
* `|ζ'(s)|, |ζ''(s)| ≤ C(1 + |t|)^N` (the corpus strip bound, and a Cauchy estimate);
* `|(χ'/χ)'(s)| (1 + |t|) ≤ C` and `|χ'/χ(s)| ≤ C (1 + log(1 + |t|))`;
* Dirichlet series on `Re w = 3/2`: `|Σ f(n) n^{−w}| ≤ Σ |f(n)| n^{−3/2}`.

Off a compact range these are the corpus bounds; on it, continuity.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

/-- A continuous function with a polynomial bound for `|t| ≥ R` has one everywhere. -/
theorem exists_bound_of_continuous_of_tail {f : ℝ → ℂ} (hf : Continuous f) {R C : ℝ} {N : ℕ}
    (h : ∀ t, R ≤ |t| → ‖f t‖ ≤ C * (1 + |t|) ^ N) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t, ‖f t‖ ≤ C' * (1 + |t|) ^ N := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max (max C M) 0, le_max_right _ _, fun t => ?_⟩
  have hpow : (1 : ℝ) ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  rcases le_or_gt R |t| with ht | ht
  · refine (h t ht).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have htI : t ∈ Icc (-R) R := by
      rw [mem_Icc]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have h1 := hM t htI
    have h2 : M ≤ max (max C M) 0 := (le_max_right _ _).trans (le_max_left _ _)
    have h3 : 0 ≤ max (max C M) 0 := le_max_right _ _
    calc ‖f t‖ ≤ M := h1
      _ ≤ max (max C M) 0 := h2
      _ ≤ max (max C M) 0 * (1 + |t|) ^ N := le_mul_of_one_le_right h3 hpow

theorem continuous_leftPt : Continuous leftPt := by unfold leftPt; fun_prop

theorem leftPt_re (t : ℝ) : (leftPt t).re = -1 / 2 := by simp [leftPt]

theorem leftPt_im (t : ℝ) : (leftPt t).im = t := by simp [leftPt]

theorem leftPt_ne_one (t : ℝ) : leftPt t ≠ 1 := ne_one_of_mem_leftStrip (leftPt_mem_leftStrip t)

theorem continuousOn_of_analytic_leftStrip {F : ℂ → ℂ}
    (hF : ∀ z ∈ leftStrip, ContinuousAt F z) : Continuous fun t => F (leftPt t) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hF _ (leftPt_mem_leftStrip t)).comp continuous_leftPt.continuousAt

/-! ## `χ` and `ζ` -/

theorem continuousAt_zetaChi_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    ContinuousAt zetaChi z :=
  (differentiableAt_zetaChi_of_mem_leftStrip hz).continuousAt

theorem exists_norm_zetaChi_leftPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖zetaChi (leftPt t)‖ ≤ C * (1 + |t|) ^ 1 := by
  refine exists_bound_of_continuous_of_tail
    (continuousOn_of_analytic_leftStrip fun z hz => continuousAt_zetaChi_of_mem_leftStrip hz)
    (R := 2) (C := Real.exp 2) fun t ht => ?_
  have h := norm_zetaChi_le_half_strip (σ := -1 / 2) (t := t) (by norm_num) (by norm_num) ht
  rw [pow_one]
  convert h using 3
  simp [leftPt]

/-- `‖Σ f(n) n^{−w}‖ ≤ Σ ‖f(n)‖ n^{−Re w}`. -/
theorem norm_LSeries_le_tsum {f : ℕ → ℂ} {w : ℂ} (hf : LSeriesSummable f w) :
    ‖LSeries f w‖ ≤ ∑' n, ‖LSeries.term f w n‖ :=
  norm_tsum_le_tsum_norm hf.norm

theorem norm_LSeries_le_of_re {f : ℕ → ℂ} {w : ℂ} {σ : ℝ} (hw : w.re = σ)
    (hf : LSeriesSummable f σ) :
    ‖LSeries f w‖ ≤ ∑' n, ‖LSeries.term f σ n‖ := by
  have hsum : LSeriesSummable f w := by
    rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
    convert hf using 2 with n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hw]
    simp
  refine (norm_LSeries_le_tsum hsum).trans (le_of_eq ?_)
  congr 1
  funext n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hw]
  simp

theorem LSeriesSummable_one_three_halves : LSeriesSummable (1 : ℕ → ℂ) ((3 / 2 : ℝ) : ℂ) :=
  LSeriesSummable_one_iff.mpr (by norm_num)

theorem exists_norm_riemannZeta_leftPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖riemannZeta (leftPt t)‖ ≤ C * (1 + |t|) ^ 1 := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_leftPt_le
  set K : ℝ := ∑' n, ‖LSeries.term (1 : ℕ → ℂ) ((3 / 2 : ℝ) : ℂ) n‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨Cχ * K, by positivity, fun t => ?_⟩
  have hz := leftPt_mem_leftStrip t
  rw [riemannZeta_eq_of_mem_leftStrip hz, norm_mul]
  have hre : (1 - leftPt t).re = 3 / 2 := by simp [leftPt]; norm_num
  have hζ : ‖riemannZeta (1 - leftPt t)‖ ≤ K := by
    rw [← LSeries_one_eq_riemannZeta (by rw [hre]; norm_num)]
    exact norm_LSeries_le_of_re hre LSeriesSummable_one_three_halves
  calc ‖zetaChi (leftPt t)‖ * ‖riemannZeta (1 - leftPt t)‖ ≤ (Cχ * (1 + |t|) ^ 1) * K :=
        mul_le_mul (hχ t) hζ (norm_nonneg _) (by positivity)
    _ = Cχ * K * (1 + |t|) ^ 1 := by ring

/-! ## Derivatives of `ζ` -/

theorem continuousAt_deriv_riemannZeta_of_ne {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt (deriv riemannZeta) z :=
  (analyticAt_riemannZeta_of_ne_one hz).deriv.continuousAt

theorem continuousAt_deriv_deriv_riemannZeta_of_ne {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt (deriv (deriv riemannZeta)) z :=
  (analyticAt_riemannZeta_of_ne_one hz).deriv.deriv.continuousAt

theorem exists_norm_deriv_riemannZeta_leftPt_le :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv riemannZeta (leftPt t)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨C, N, hC0, hC⟩ := RHTower.exists_bound_norm_deriv_riemannZeta_strip 1
  obtain ⟨C', hC'0, hC'⟩ := exists_bound_of_continuous_of_tail
    (continuousOn_of_analytic_leftStrip fun z hz =>
      continuousAt_deriv_riemannZeta_of_ne (ne_one_of_mem_leftStrip hz))
    (R := 2) (C := C * 2 ^ N) (N := N) fun t ht => by
      have h := hC (leftPt t) (by rw [leftPt_re]; norm_num) (by rw [leftPt_im]; exact ht)
      rw [leftPt_im] at h
      refine h.trans ?_
      rw [mul_pow, mul_assoc]
      gcongr
      linarith
  exact ⟨C', N, hC'0, hC'⟩

theorem exists_norm_deriv_deriv_riemannZeta_leftPt_le :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv (deriv riemannZeta) (leftPt t)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨C, N, hC0, hC⟩ := RHTower.exists_bound_norm_deriv_riemannZeta_strip 1
  obtain ⟨C', hC'0, hC'⟩ := exists_bound_of_continuous_of_tail
    (continuousOn_of_analytic_leftStrip fun z hz =>
      continuousAt_deriv_deriv_riemannZeta_of_ne (ne_one_of_mem_leftStrip hz))
    (R := 3) (C := 2 * (C * 4 ^ N)) (N := N) fun t ht => by
      -- Cauchy's estimate on the circle of radius `½`
      have hball : DiffContOnCl ℂ (deriv riemannZeta) (Metric.ball (leftPt t) (1 / 2)) := by
        refine DifferentiableOn.diffContOnCl ?_
        intro z hz
        have hz' : z ∈ Metric.closedBall (leftPt t) (1 / 2) := by
          rw [closure_ball _ (by norm_num)] at hz; exact hz
        have hre : |z.re - (-1 / 2)| ≤ 1 / 2 := by
          have := Complex.abs_re_le_norm (z - leftPt t)
          rw [Complex.sub_re, leftPt_re] at this
          exact this.trans (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz')
        have hz1 : z ≠ 1 := by
          intro h; rw [h] at hre; simp at hre; rw [abs_of_pos (by norm_num)] at hre; norm_num at hre
        exact (analyticAt_riemannZeta_of_ne_one hz1).deriv.differentiableAt.differentiableWithinAt
      have hsph : ∀ z ∈ Metric.sphere (leftPt t) (1 / 2),
          ‖deriv riemannZeta z‖ ≤ C * 4 ^ N * (1 + |t|) ^ N := by
        intro z hz
        have hd : ‖z - leftPt t‖ = 1 / 2 := by rw [← dist_eq_norm]; exact hz
        have hre := Complex.abs_re_le_norm (z - leftPt t)
        have him := Complex.abs_im_le_norm (z - leftPt t)
        rw [hd, Complex.sub_re, leftPt_re] at hre
        rw [hd, Complex.sub_im, leftPt_im] at him
        have hzre : |z.re| ≤ 1 := by
          rw [abs_le] at hre ⊢; constructor <;> linarith
        have hzim : 2 ≤ |z.im| := by
          have := abs_sub_abs_le_abs_sub z.im t
          rw [abs_sub_comm] at him
          linarith [abs_sub_abs_le_abs_sub t z.im]
        refine (hC z hzre hzim).trans ?_
        have hzim2 : |z.im| ≤ |t| + 1 / 2 := by
          have := abs_sub_abs_le_abs_sub z.im t; linarith
        have h1 : 2 * |z.im| ≤ 4 * (1 + |t|) := by linarith
        calc C * (2 * |z.im|) ^ N ≤ C * (4 * (1 + |t|)) ^ N := by
              gcongr
          _ = C * 4 ^ N * (1 + |t|) ^ N := by rw [mul_pow]; ring
      have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hball hsph
      calc ‖deriv (deriv riemannZeta) (leftPt t)‖ ≤ C * 4 ^ N * (1 + |t|) ^ N / (1 / 2) := h
        _ = 2 * (C * 4 ^ N) * (1 + |t|) ^ N := by ring
  exact ⟨C', N, hC'0, hC'⟩

/-! ## `χ'/χ` and its derivative -/

theorem continuousAt_logDeriv_zetaChi {z : ℂ} (hz : z ∈ leftStrip) :
    ContinuousAt (logDeriv zetaChi) z := by
  have hχan := zetaChi_analyticAt (gammaR_one_sub_ne_zero_of_mem_leftStrip hz)
  have : logDeriv zetaChi = fun w => deriv zetaChi w / zetaChi w := by
    funext w; exact logDeriv_apply _ _
  rw [this]
  exact hχan.deriv.continuousAt.div hχan.continuousAt (zetaChi_ne_zero_of_mem_leftStrip hz)

theorem analyticAt_logDeriv_zetaChi {z : ℂ} (hz : z ∈ leftStrip) :
    AnalyticAt ℂ (logDeriv zetaChi) z := by
  have hχan := zetaChi_analyticAt (gammaR_one_sub_ne_zero_of_mem_leftStrip hz)
  have : logDeriv zetaChi = fun w => deriv zetaChi w / zetaChi w := by
    funext w; exact logDeriv_apply _ _
  rw [this]
  exact hχan.deriv.div hχan (zetaChi_ne_zero_of_mem_leftStrip hz)

theorem continuousAt_deriv_logDeriv_zetaChi {z : ℂ} (hz : z ∈ leftStrip) :
    ContinuousAt (deriv (logDeriv zetaChi)) z := by
  have hev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (logDeriv zetaChi) w := by
    filter_upwards [isOpen_leftStrip.mem_nhds hz] with w hw
    exact analyticAt_logDeriv_zetaChi hw
  exact ((analyticAt_logDeriv_zetaChi hz).deriv).continuousAt

/-- `|(χ'/χ)'(−½ + it)| (1 + |t|) ≤ C`. -/
theorem exists_norm_deriv_logDeriv_zetaChi_leftPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv (logDeriv zetaChi) (leftPt t)‖ * (1 + |t|) ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (continuousOn_of_analytic_leftStrip fun z hz =>
      continuousAt_deriv_logDeriv_zetaChi hz).continuousOn
  refine ⟨max (3 * M) 10, le_trans (by norm_num) (le_max_right _ _), fun t => ?_⟩
  rcases le_or_gt 2 |t| with ht | ht
  · have h := RHTower.norm_iteratedDeriv_logDeriv_zetaChi_le (n := 1) le_rfl (z := leftPt t)
      (by rw [leftPt_re]; norm_num) (by rw [leftPt_re]; norm_num) (by rw [leftPt_im]; exact ht)
    rw [iteratedDeriv_one, leftPt_im] at h
    simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one] at h
    have ht0 : 0 < |t| := by linarith
    calc ‖deriv (logDeriv zetaChi) (leftPt t)‖ * (1 + |t|) ≤ 5 / |t| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = 5 / |t| + 5 := by field_simp
      _ ≤ 10 := by
          have : 5 / |t| ≤ 5 := by rw [div_le_iff₀ ht0]; linarith
          linarith
      _ ≤ max (3 * M) 10 := le_max_right _ _
  · have htI : t ∈ Icc (-2 : ℝ) 2 := by
      rw [mem_Icc]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have h1 := hM t htI
    have hM0 : 0 ≤ M := (norm_nonneg _).trans h1
    calc ‖deriv (logDeriv zetaChi) (leftPt t)‖ * (1 + |t|) ≤ M * 3 :=
          mul_le_mul h1 (by linarith) (by positivity) hM0
      _ = 3 * M := by ring
      _ ≤ max (3 * M) 10 := le_max_left _ _

/-- `|χ'/χ(−½ + it)| ≤ C (1 + log(1 + |t|))`. -/
theorem exists_norm_logDeriv_zetaChi_leftPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖logDeriv zetaChi (leftPt t)‖ ≤ C * (1 + Real.log (1 + |t|)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    (continuousOn_of_analytic_leftStrip fun z hz => continuousAt_logDeriv_zetaChi hz).continuousOn
  set L : ℝ := Real.log (2 * Real.pi) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨max M (5 + L), le_trans (by linarith) (le_max_right _ _), fun t => ?_⟩
  have hlog0 : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  rcases le_or_gt 4 |t| with ht | ht
  · have hlin : leftPt t = RHTower.linePt t + (-1 : ℂ) := by
      simp only [leftPt, RHTower.linePt]; push_cast; ring
    have h := RHTower.ZetaNotch.norm_logDeriv_zetaChi_linePt_add_log_le (τ := t) ht (u := -1)
      (by simp) (by simp) (by simp)
    rw [← hlin] at h
    have ht0 : 0 < |t| := by linarith
    have hsmall : 10 * ‖(-1 : ℂ)‖ / |t| + 26 / t ^ 2 ≤ 5 := by
      rw [norm_neg, norm_one, mul_one]
      have h1 : 10 / |t| ≤ 3 := by rw [div_le_iff₀ ht0]; linarith
      have h2 : 26 / t ^ 2 ≤ 2 := by
        have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
        rw [div_le_iff₀ ht2, ← sq_abs]; nlinarith
      linarith
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hlogt : |Real.log (|t| / (2 * Real.pi))| ≤ Real.log (1 + |t|) + L := by
      rw [Real.log_div ht0.ne' h2pi.ne']
      have h1 : Real.log |t| ≤ Real.log (1 + |t|) := Real.log_le_log ht0 (by linarith)
      have h2 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
      rw [abs_le]; constructor <;> linarith
    have hnorm : ‖logDeriv zetaChi (leftPt t)‖ ≤ Real.log (1 + |t|) + (5 + L) := by
      have := norm_sub_le (logDeriv zetaChi (leftPt t) + (Real.log (|t| / (2 * Real.pi)) : ℂ))
        (Real.log (|t| / (2 * Real.pi)) : ℂ)
      rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    calc ‖logDeriv zetaChi (leftPt t)‖ ≤ Real.log (1 + |t|) + (5 + L) := hnorm
      _ ≤ (5 + L) * (1 + Real.log (1 + |t|)) := by nlinarith
      _ ≤ max M (5 + L) * (1 + Real.log (1 + |t|)) := by gcongr; exact le_max_right _ _
  · have htI : t ∈ Icc (-4 : ℝ) 4 := by
      rw [mem_Icc]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have h1 := hM t htI
    calc ‖logDeriv zetaChi (leftPt t)‖ ≤ M := h1
      _ ≤ max M (5 + L) := le_max_left _ _
      _ ≤ max M (5 + L) * (1 + Real.log (1 + |t|)) :=
          le_mul_of_one_le_right (le_trans (by linarith) (le_max_right _ _)) (by linarith)

/-- `χ' = χ · χ'/χ` on the strip. -/
theorem deriv_zetaChi_eq_mul_logDeriv {z : ℂ} (hz : z ∈ leftStrip) :
    deriv zetaChi z = zetaChi z * logDeriv zetaChi z := by
  rw [logDeriv_apply]
  field_simp [zetaChi_ne_zero_of_mem_leftStrip hz]

theorem exists_norm_deriv_zetaChi_leftPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv zetaChi (leftPt t)‖ ≤ C * (1 + |t|) ^ 2 := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_norm_zetaChi_leftPt_le
  obtain ⟨CD, hCD0, hCD⟩ := exists_norm_logDeriv_zetaChi_leftPt_le
  refine ⟨Cχ * CD, by positivity, fun t => ?_⟩
  rw [deriv_zetaChi_eq_mul_logDeriv (leftPt_mem_leftStrip t), norm_mul]
  have hlog : Real.log (1 + |t|) ≤ |t| := by
    have := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : (0 : ℝ) < 1 + |t|)
    linarith
  have h1 := hCχ t
  have h2 := hCD t
  have h3 : CD * (1 + Real.log (1 + |t|)) ≤ CD * (1 + |t|) := by gcongr
  calc ‖zetaChi (leftPt t)‖ * ‖logDeriv zetaChi (leftPt t)‖
      ≤ (Cχ * (1 + |t|) ^ 1) * (CD * (1 + |t|)) :=
        mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
    _ = Cχ * CD * (1 + |t|) ^ 2 := by ring

end

end RHTower.GaussZeroSum
