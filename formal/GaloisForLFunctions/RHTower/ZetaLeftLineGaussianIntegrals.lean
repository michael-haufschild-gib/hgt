import GaloisForLFunctions.RHTower.ZetaLeftLineBounds

/-!
# Gaussian integrals along `Re s = −½`

With `G(s) = r^s g_T(s)`, `r > 0`, `T ≥ 1`, and `s_t = −½ + it`:

* (`integral_zetaChi_mul_LSeries`) for `Σ |c(n)| n^{−3/2} < ∞`,
  `∫ χ(s_t) (Σ c(n) n^{s_t − 1}) G(s_t) dt = 2π r Σ_{n ≥ 1} c(n) J_T(nr)`: integrate the series
  termwise against the exact kernel identity;
* (`integral_deriv_deriv_riemannZeta_mul`) `∫ ζ''(s_t) G(s_t) dt = ∫ ζ(s_t) G''(s_t) dt`, by two
  integrations by parts along the line;
* Gaussian moments `∫ (1 + |t|)^N e^{(1 − t²)/T²} dt ≤ C_N T^{N+1}`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

/-! ## Gaussian moments in `t` -/

/-- `(1 + |t|)^N e^{−t²/T²} ≤ N! e^{3/2} T^N e^{−t²/(2T²)}` for `T ≥ 1`. -/
theorem one_add_abs_pow_mul_exp_le (N : ℕ) {T : ℝ} (hT : 1 ≤ T) (t : ℝ) :
    (1 + |t|) ^ N * Real.exp (-(t ^ 2 / T ^ 2)) ≤
      N.factorial * Real.exp (3 / 2) * T ^ N * Real.exp (-(t ^ 2 / (2 * T ^ 2))) := by
  have hT0 : 0 < T := by linarith
  set v : ℝ := |t| / T with hv
  have hv0 : 0 ≤ v := by positivity
  have h1 : 1 + |t| ≤ T * (1 + v) := by
    rw [hv, mul_add, mul_div_cancel₀ _ hT0.ne']; linarith
  have h2 : (1 + v) ^ N ≤ N.factorial * Real.exp (1 + v) := by
    have := Real.pow_div_factorial_le_exp (1 + v) (by linarith) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    rw [div_le_iff₀ hf] at this; linarith
  have hsq : t ^ 2 / T ^ 2 = v ^ 2 := by rw [hv, div_pow, sq_abs]
  have hsq2 : t ^ 2 / (2 * T ^ 2) = v ^ 2 / 2 := by rw [← hsq]; field_simp
  have h3 : Real.exp (1 + v) * Real.exp (-(v ^ 2)) ≤ Real.exp (3 / 2) * Real.exp (-(v ^ 2 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (v - 1)]
  rw [hsq, hsq2]
  calc (1 + |t|) ^ N * Real.exp (-v ^ 2) ≤ (T * (1 + v)) ^ N * Real.exp (-v ^ 2) := by
        gcongr
    _ = T ^ N * (1 + v) ^ N * Real.exp (-v ^ 2) := by rw [mul_pow]
    _ ≤ T ^ N * (N.factorial * Real.exp (1 + v)) * Real.exp (-v ^ 2) := by gcongr
    _ = N.factorial * T ^ N * (Real.exp (1 + v) * Real.exp (-v ^ 2)) := by ring
    _ ≤ N.factorial * T ^ N * (Real.exp (3 / 2) * Real.exp (-(v ^ 2 / 2))) := by gcongr
    _ = _ := by ring

theorem integrable_exp_half_gauss {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / (2 * T ^ 2)))) := by
  have h := integrable_exp_neg_mul_sq (b := 1 / (2 * T ^ 2)) (by positivity)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  ring

theorem integral_exp_half_gauss {T : ℝ} (hT : 0 < T) :
    ∫ t : ℝ, Real.exp (-(t ^ 2 / (2 * T ^ 2))) = Real.sqrt (2 * Real.pi) * T := by
  have h := integral_gaussian (1 / (2 * T ^ 2))
  have e : (fun x : ℝ => Real.exp (-(1 / (2 * T ^ 2)) * x ^ 2)) =
      fun t => Real.exp (-(t ^ 2 / (2 * T ^ 2))) := by
    funext t; congr 1; ring
  rw [e] at h
  rw [h, show Real.pi / (1 / (2 * T ^ 2)) = (2 * Real.pi) * T ^ 2 by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hT.le]

/-- A continuous function bounded by `C (1 + |t|)^N e^{(1 − t²)/T²}` is integrable. -/
theorem integrable_of_poly_gauss {F : ℝ → ℂ} (hF : Continuous F) {C T : ℝ} {N : ℕ} (hT : 1 ≤ T)
    (h : ∀ t, ‖F t‖ ≤ C * (1 + |t|) ^ N * Real.exp ((1 - t ^ 2) / T ^ 2)) : Integrable F := by
  have hT0 : 0 < T := by linarith
  refine ((integrable_exp_half_gauss hT0).const_mul
    (|C| * Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N))).mono' hF.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  refine (h t).trans ?_
  have hsplit : Real.exp ((1 - t ^ 2) / T ^ 2) = Real.exp (1 / T ^ 2) * Real.exp (-(t ^ 2 / T ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : Real.exp (1 / T ^ 2) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    rw [div_le_one (by positivity)]; nlinarith
  have hp := one_add_abs_pow_mul_exp_le N hT t
  rw [hsplit]
  calc C * (1 + |t|) ^ N * (Real.exp (1 / T ^ 2) * Real.exp (-(t ^ 2 / T ^ 2)))
      ≤ |C| * Real.exp 1 * ((1 + |t|) ^ N * Real.exp (-(t ^ 2 / T ^ 2))) := by
        have h0 : 0 ≤ (1 + |t|) ^ N * Real.exp (-(t ^ 2 / T ^ 2)) := by positivity
        calc C * (1 + |t|) ^ N * (Real.exp (1 / T ^ 2) * Real.exp (-(t ^ 2 / T ^ 2)))
            = C * Real.exp (1 / T ^ 2) * ((1 + |t|) ^ N * Real.exp (-(t ^ 2 / T ^ 2))) := by ring
          _ ≤ |C| * Real.exp 1 * ((1 + |t|) ^ N * Real.exp (-(t ^ 2 / T ^ 2))) := by
              apply mul_le_mul_of_nonneg_right _ h0
              exact mul_le_mul (le_abs_self C) hE (Real.exp_pos _).le (abs_nonneg C)
    _ ≤ |C| * Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N *
          Real.exp (-(t ^ 2 / (2 * T ^ 2)))) := by gcongr
    _ = _ := by ring

/-- `∫ (1 + |t|)^N e^{(1 − t²)/T²} dt ≤ N! e^{5/2} √(2π) T^{N+1}`. -/
theorem integral_poly_gauss_le (N : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t : ℝ, (1 + |t|) ^ N * Real.exp ((1 - t ^ 2) / T ^ 2) ≤
      N.factorial * Real.exp (5 / 2) * Real.sqrt (2 * Real.pi) * T ^ (N + 1) := by
  have hT0 : 0 < T := by linarith
  have hmaj : ∀ t : ℝ, (1 + |t|) ^ N * Real.exp ((1 - t ^ 2) / T ^ 2) ≤
      Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N) * Real.exp (-(t ^ 2 / (2 * T ^ 2))) := by
    intro t
    have hsplit : Real.exp ((1 - t ^ 2) / T ^ 2) =
        Real.exp (1 / T ^ 2) * Real.exp (-(t ^ 2 / T ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hE : Real.exp (1 / T ^ 2) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      rw [div_le_one (by positivity)]; nlinarith
    have hp := one_add_abs_pow_mul_exp_le N hT t
    rw [hsplit]
    calc (1 + |t|) ^ N * (Real.exp (1 / T ^ 2) * Real.exp (-(t ^ 2 / T ^ 2)))
        = Real.exp (1 / T ^ 2) * ((1 + |t|) ^ N * Real.exp (-(t ^ 2 / T ^ 2))) := by ring
      _ ≤ Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N *
            Real.exp (-(t ^ 2 / (2 * T ^ 2)))) := by
          apply mul_le_mul hE hp (by positivity) (Real.exp_pos _).le
      _ = _ := by ring
  have hint : Integrable (fun t : ℝ => (1 + |t|) ^ N * Real.exp ((1 - t ^ 2) / T ^ 2)) := by
    refine ((integrable_exp_half_gauss hT0).const_mul
      (Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N))).mono'
      (by fun_prop) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmaj t
  calc ∫ t : ℝ, (1 + |t|) ^ N * Real.exp ((1 - t ^ 2) / T ^ 2)
      ≤ ∫ t : ℝ, Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N) *
          Real.exp (-(t ^ 2 / (2 * T ^ 2))) :=
        integral_mono hint ((integrable_exp_half_gauss hT0).const_mul _) hmaj
    _ = Real.exp 1 * (N.factorial * Real.exp (3 / 2) * T ^ N) * (Real.sqrt (2 * Real.pi) * T) := by
        rw [integral_const_mul, integral_exp_half_gauss hT0]
    _ = N.factorial * (Real.exp 1 * Real.exp (3 / 2)) * Real.sqrt (2 * Real.pi) * T ^ (N + 1) := by
        ring
    _ = _ := by rw [← Real.exp_add]; norm_num

theorem integrable_poly_gauss_real (N : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ => (1 + |t|) ^ N * Real.exp ((1 - t ^ 2) / T ^ 2)) := by
  have h := integrable_of_poly_gauss (F := fun t : ℝ => (((1 + |t|) ^ N *
    Real.exp ((1 - t ^ 2) / T ^ 2) : ℝ) : ℂ)) (by fun_prop) (C := 1) (N := N) hT fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
  exact h.re.congr (Eventually.of_forall fun t => Complex.ofReal_re _)

/-! ## Termwise integration of a Dirichlet series against `χ` -/

theorem norm_cpow_leftPt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖(r : ℂ) ^ leftPt t‖ = r ^ (-1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, leftPt_re]

theorem norm_term_one_sub_leftPt (c : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    ‖LSeries.term c (1 - leftPt t) n‖ = ‖LSeries.term c ((3 / 2 : ℝ) : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  have : (1 - leftPt t).re = ((3 / 2 : ℝ) : ℂ).re := by simp [leftPt]; norm_num
  rw [this]

theorem term_one_sub_leftPt_mul {c : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    LSeries.term c (1 - leftPt t) n * (r : ℂ) ^ leftPt t =
      (c n / n) * (((n * r : ℝ) : ℂ) ^ leftPt t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hn0.le hr.le, Complex.cpow_sub _ _ (by exact_mod_cast hn),
    Complex.cpow_one]
  have hc : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; ring
  rw [hc]
  have hne : (n : ℂ) ^ leftPt t ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero]
    · exact_mod_cast hn
    · intro h; have := congrArg Complex.re h; simp [leftPt] at this
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem continuous_zetaChi_leftPt : Continuous fun t => zetaChi (leftPt t) :=
  continuousOn_of_analytic_leftStrip fun _ hz => continuousAt_zetaChi_of_mem_leftStrip hz

theorem continuous_cpow_leftPt {r : ℝ} (hr : 0 < r) : Continuous fun t => (r : ℂ) ^ leftPt t :=
  continuous_leftPt.const_cpow (Or.inl (by exact_mod_cast hr.ne'))

theorem continuous_gaussWeight_leftPt (T : ℝ) : Continuous fun t => gaussWeight T (leftPt t) := by
  unfold gaussWeight; have := continuous_leftPt; fun_prop

theorem continuous_term_one_sub_leftPt (c : ℕ → ℂ) (n : ℕ) :
    Continuous fun t => LSeries.term c (1 - leftPt t) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero]; exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    refine continuous_const.div ?_ fun t => ?_
    · exact (continuous_const.sub continuous_leftPt).const_cpow (Or.inl (by exact_mod_cast hn))
    · rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero]
      · exact_mod_cast hn
      · intro h; have := congrArg Complex.re h; simp [leftPt] at this; norm_num at this

/-- **Termwise integration.**  For `Σ |c(n)| n^{−3/2} < ∞`,
`∫ χ(s_t) (Σ c(n) n^{s_t−1}) r^{s_t} g_T(s_t) dt = 2π r Σ_{n ≥ 1} c(n) J_T(nr)`. -/
theorem integral_zetaChi_mul_LSeries {c : ℕ → ℂ} (hc : LSeriesSummable c ((3 / 2 : ℝ) : ℂ))
    {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    ∫ t : ℝ, zetaChi (leftPt t) * LSeries c (1 - leftPt t) *
        ((r : ℂ) ^ leftPt t * gaussWeight T (leftPt t)) =
      2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then 0 else c n * leftKernel T (n * r)) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_norm_zetaChi_leftPt_le
  set F : ℕ → ℝ → ℂ := fun n t => zetaChi (leftPt t) * LSeries.term c (1 - leftPt t) n *
    ((r : ℂ) ^ leftPt t * gaussWeight T (leftPt t)) with hF
  set M : ℝ → ℝ := fun t => Cχ * r ^ (-1 / 2 : ℝ) * ((1 + |t|) ^ 1 *
    Real.exp ((1 - t ^ 2) / T ^ 2)) with hM
  have hMint : Integrable M := (integrable_poly_gauss_real 1 hT).const_mul _
  have hbound : ∀ n t, ‖F n t‖ ≤ ‖LSeries.term c ((3 / 2 : ℝ) : ℂ) n‖ * M t := by
    intro n t
    simp only [hF, hM]
    rw [norm_mul, norm_mul, norm_mul, norm_term_one_sub_leftPt, norm_cpow_leftPt hr,
      norm_gaussWeight_leftPt]
    have h1 := hCχ t
    calc ‖zetaChi (leftPt t)‖ * ‖LSeries.term c ((3 / 2 : ℝ) : ℂ) n‖ *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
        ≤ (Cχ * (1 + |t|) ^ 1) * ‖LSeries.term c ((3 / 2 : ℝ) : ℂ) n‖ *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by gcongr
      _ = _ := by ring
  have hcont : ∀ n, Continuous (F n) := fun n =>
    (continuous_zetaChi_leftPt.mul (continuous_term_one_sub_leftPt c n)).mul
      ((continuous_cpow_leftPt hr).mul (continuous_gaussWeight_leftPt T))
  have hint : ∀ n, Integrable (F n) := fun n =>
    (hMint.const_mul ‖LSeries.term c ((3 / 2 : ℝ) : ℂ) n‖).mono' (hcont n).aestronglyMeasurable
      (Eventually.of_forall (hbound n))
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_) (hc.norm.mul_right (∫ t, M t))
    rw [← integral_const_mul]
    exact integral_mono (hint n).norm (hMint.const_mul _) (hbound n)
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hpt : ∀ t, ∑' n, F n t = zetaChi (leftPt t) * LSeries c (1 - leftPt t) *
      ((r : ℂ) ^ leftPt t * gaussWeight T (leftPt t)) := by
    intro t
    simp only [hF, LSeries]
    rw [tsum_mul_right, tsum_mul_left]
  simp_rw [hpt] at hswap
  rw [← hswap, ← tsum_mul_left]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hF]
  · rw [if_neg hn]
    have hpos : 0 < (n : ℝ) * r := by
      have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      positivity
    have hF' : F n = fun t => (c n / n) * (zetaChi (leftPt t) * (((n * r : ℝ) : ℂ) ^ leftPt t) *
        gaussWeight T (leftPt t)) := by
      funext t
      simp only [hF]
      have h := term_one_sub_leftPt_mul (c := c) hn hr t
      calc zetaChi (leftPt t) * LSeries.term c (1 - leftPt t) n *
            ((r : ℂ) ^ leftPt t * gaussWeight T (leftPt t))
          = zetaChi (leftPt t) * (LSeries.term c (1 - leftPt t) n * (r : ℂ) ^ leftPt t) *
              gaussWeight T (leftPt t) := by ring
        _ = _ := by rw [h]; ring
    rw [hF', integral_const_mul, integral_zetaChi_mul_cpow_mul_gaussWeight hT hpos]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp

/-! ## Two integrations by parts for `ζ''` -/

/-- `G(s) = r^s g_T(s)`. -/
def gW (T r : ℝ) (s : ℂ) : ℂ := (r : ℂ) ^ s * gaussWeight T s

/-- `G' = (log r + 2(s − ½)/T²) G`. -/
def gW1 (T r : ℝ) (s : ℂ) : ℂ := ((Real.log r : ℂ) + 2 * (s - 1 / 2) / (T : ℂ) ^ 2) * gW T r s

/-- `G'' = ((log r + 2(s − ½)/T²)² + 2/T²) G`. -/
def gW2 (T r : ℝ) (s : ℂ) : ℂ :=
  (((Real.log r : ℂ) + 2 * (s - 1 / 2) / (T : ℂ) ^ 2) ^ 2 + 2 / (T : ℂ) ^ 2) * gW T r s

theorem hasDerivAt_gaussWeight (T : ℝ) (s : ℂ) :
    HasDerivAt (gaussWeight T) (2 * (s - 1 / 2) / (T : ℂ) ^ 2 * gaussWeight T s) s := by
  have h : HasDerivAt (fun z : ℂ => (z - 1 / 2) ^ 2 / (T : ℂ) ^ 2) (2 * (s - 1 / 2) / (T : ℂ) ^ 2) s := by
    have := (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).pow 2).div_const ((T : ℂ) ^ 2)
    refine this.congr_deriv ?_
    simp
  have h2 := h.cexp
  refine h2.congr_deriv ?_
  unfold gaussWeight
  ring

theorem hasDerivAt_gW {T r : ℝ} (hr : 0 < r) (s : ℂ) : HasDerivAt (gW T r) (gW1 T r s) s := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : HasDerivAt (fun z : ℂ => (r : ℂ) ^ z) ((r : ℂ) ^ s * Complex.log r) s :=
    (hasStrictDerivAt_const_cpow (Or.inl hr0)).hasDerivAt
  have h := hc.mul (hasDerivAt_gaussWeight T s)
  refine h.congr_deriv ?_
  unfold gW1 gW
  rw [← Complex.ofReal_log hr.le]
  ring

theorem hasDerivAt_gW1 {T r : ℝ} (hr : 0 < r) (s : ℂ) : HasDerivAt (gW1 T r) (gW2 T r s) s := by
  have hl : HasDerivAt (fun z : ℂ => (Real.log r : ℂ) + 2 * (z - 1 / 2) / (T : ℂ) ^ 2)
      (2 / (T : ℂ) ^ 2) s := by
    have := (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul (2 : ℂ)).div_const ((T : ℂ) ^ 2)
    refine (this.const_add (Real.log r : ℂ)).congr_deriv ?_
    simp
  have h := hl.mul (hasDerivAt_gW (T := T) hr s)
  refine h.congr_deriv ?_
  unfold gW2 gW1
  ring

theorem hasDerivAt_leftPt (t : ℝ) : HasDerivAt leftPt I t := by
  have := ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (-1 / 2 : ℂ)
  simpa [leftPt] using this

/-- Composition with the line `t ↦ −½ + it`. -/
theorem hasDerivAt_comp_leftPt {F : ℂ → ℂ} {F' : ℂ} {t : ℝ} (h : HasDerivAt F F' (leftPt t)) :
    HasDerivAt (fun u => F (leftPt u)) (F' * I) t :=
  h.comp t (hasDerivAt_leftPt t)

theorem norm_gW_leftPt {T r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖gW T r (leftPt t)‖ = r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) := by
  unfold gW
  rw [norm_mul, norm_cpow_leftPt hr, norm_gaussWeight_leftPt]

theorem norm_leftPt_sub_half_le (t : ℝ) : ‖leftPt t - 1 / 2‖ ≤ 1 + |t| := by
  have e : leftPt t - 1 / 2 = -1 + (t : ℂ) * I := by simp only [leftPt]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem norm_affine_le {T r : ℝ} (hT : 1 ≤ T) (t : ℝ) :
    ‖(Real.log r : ℂ) + 2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2‖ ≤ (|Real.log r| + 2) * (1 + |t|) := by
  have hT2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_div, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < T)]
  have h1 := norm_leftPt_sub_half_le t
  have h2 : ‖(2 : ℂ)‖ * ‖leftPt t - 1 / 2‖ / T ^ 2 ≤ 2 * (1 + |t|) := by
    rw [div_le_iff₀ (by positivity)]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    nlinarith [norm_nonneg (leftPt t - 1 / 2), abs_nonneg t]
  have h3 : |Real.log r| ≤ |Real.log r| * (1 + |t|) := le_mul_of_one_le_right (abs_nonneg _)
    (by linarith [abs_nonneg t])
  nlinarith

theorem norm_gW1_leftPt_le {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) (t : ℝ) :
    ‖gW1 T r (leftPt t)‖ ≤ (|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 1 *
      Real.exp ((1 - t ^ 2) / T ^ 2) := by
  unfold gW1
  rw [norm_mul, norm_gW_leftPt hr]
  have h := norm_affine_le (r := r) hT t
  calc ‖(Real.log r : ℂ) + 2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2‖ *
        (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
      ≤ ((|Real.log r| + 2) * (1 + |t|)) * (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by
        gcongr
    _ = _ := by ring

theorem norm_gW2_leftPt_le {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) (t : ℝ) :
    ‖gW2 T r (leftPt t)‖ ≤ ((|Real.log r| + 2) ^ 2 + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 2 *
      Real.exp ((1 - t ^ 2) / T ^ 2) := by
  unfold gW2
  rw [norm_mul, norm_gW_leftPt hr]
  have h := norm_affine_le (r := r) hT t
  have hT2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
  have h2 : ‖(2 : ℂ) / (T : ℂ) ^ 2‖ ≤ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < T), show ‖(2 : ℂ)‖ = 2 by norm_num,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hsq : ‖((Real.log r : ℂ) + 2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) ^ 2 + 2 / (T : ℂ) ^ 2‖ ≤
      ((|Real.log r| + 2) ^ 2 + 2) * (1 + |t|) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow]
    have h1t : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg t])
    have := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow] at this
    nlinarith
  calc ‖((Real.log r : ℂ) + 2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) ^ 2 + 2 / (T : ℂ) ^ 2‖ *
        (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
      ≤ (((|Real.log r| + 2) ^ 2 + 2) * (1 + |t|) ^ 2) *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by gcongr
    _ = _ := by ring

theorem continuous_gW_leftPt {T r : ℝ} (hr : 0 < r) : Continuous fun t => gW T r (leftPt t) :=
  (continuous_cpow_leftPt hr).mul (continuous_gaussWeight_leftPt T)

theorem continuous_gW1_leftPt {T r : ℝ} (hr : 0 < r) : Continuous fun t => gW1 T r (leftPt t) := by
  unfold gW1
  exact ((continuous_const.add ((continuous_const.mul (continuous_leftPt.sub continuous_const)).div_const
    _))).mul (continuous_gW_leftPt hr)

theorem continuous_gW2_leftPt {T r : ℝ} (hr : 0 < r) : Continuous fun t => gW2 T r (leftPt t) := by
  unfold gW2
  exact (((continuous_const.add ((continuous_const.mul (continuous_leftPt.sub continuous_const)).div_const
    _)).pow 2).add continuous_const).mul (continuous_gW_leftPt hr)

theorem continuous_riemannZeta_leftPt : Continuous fun t => riemannZeta (leftPt t) :=
  continuousOn_of_analytic_leftStrip fun _ hz =>
    (differentiableAt_riemannZeta (ne_one_of_mem_leftStrip hz)).continuousAt

theorem continuous_deriv_riemannZeta_leftPt : Continuous fun t => deriv riemannZeta (leftPt t) :=
  continuousOn_of_analytic_leftStrip fun _ hz =>
    continuousAt_deriv_riemannZeta_of_ne (ne_one_of_mem_leftStrip hz)

theorem continuous_deriv_deriv_riemannZeta_leftPt :
    Continuous fun t => deriv (deriv riemannZeta) (leftPt t) :=
  continuousOn_of_analytic_leftStrip fun _ hz =>
    continuousAt_deriv_deriv_riemannZeta_of_ne (ne_one_of_mem_leftStrip hz)

/-- **Two integrations by parts**: `∫ ζ''(s_t) G(s_t) dt = ∫ ζ(s_t) G''(s_t) dt`. -/
theorem integral_deriv_deriv_riemannZeta_mul {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    ∫ t : ℝ, gW T r (leftPt t) * deriv (deriv riemannZeta) (leftPt t) =
      ∫ t : ℝ, gW2 T r (leftPt t) * riemannZeta (leftPt t) := by
  obtain ⟨C0, hC00, hC0⟩ := exists_norm_riemannZeta_leftPt_le
  obtain ⟨C1, N1, hC10, hC1⟩ := exists_norm_deriv_riemannZeta_leftPt_le
  obtain ⟨C2, N2, hC20, hC2⟩ := exists_norm_deriv_deriv_riemannZeta_leftPt_le
  have hd0 : ∀ t, HasDerivAt (fun u => riemannZeta (leftPt u))
      (deriv riemannZeta (leftPt t) * I) t := fun t =>
    hasDerivAt_comp_leftPt (differentiableAt_riemannZeta (leftPt_ne_one t)).hasDerivAt
  have hd1 : ∀ t, HasDerivAt (fun u => deriv riemannZeta (leftPt u))
      (deriv (deriv riemannZeta) (leftPt t) * I) t := fun t =>
    hasDerivAt_comp_leftPt
      (analyticAt_riemannZeta_of_ne_one (leftPt_ne_one t)).deriv.differentiableAt.hasDerivAt
  have hg0 : ∀ t, HasDerivAt (fun u => gW T r (leftPt u)) (gW1 T r (leftPt t) * I) t := fun t =>
    hasDerivAt_comp_leftPt (hasDerivAt_gW hr _)
  have hg1 : ∀ t, HasDerivAt (fun u => gW1 T r (leftPt u)) (gW2 T r (leftPt t) * I) t := fun t =>
    hasDerivAt_comp_leftPt (hasDerivAt_gW1 hr _)
  -- the first integration by parts
  have h1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t => gW T r (leftPt t)) (v := fun t => deriv riemannZeta (leftPt t))
    (u' := fun t => gW1 T r (leftPt t) * I) (v' := fun t => deriv (deriv riemannZeta) (leftPt t) * I)
    (fun t _ => hg0 t) (fun t _ => hd1 t)
    (integrable_of_poly_gauss ((continuous_gW_leftPt hr).mul
      (continuous_deriv_deriv_riemannZeta_leftPt.mul continuous_const)) hT
      (C := r ^ (-1 / 2 : ℝ) * C2) (N := N2) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_gW_leftPt hr]
        have := hC2 t
        calc r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) *
              ‖deriv (deriv riemannZeta) (leftPt t)‖
            ≤ r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * (C2 * (1 + |t|) ^ N2) := by gcongr
          _ = _ := by ring)
    (integrable_of_poly_gauss (((continuous_gW1_leftPt hr).mul continuous_const).mul
      continuous_deriv_riemannZeta_leftPt) hT
      (C := (|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * C1) (N := 1 + N1) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        have h1 := norm_gW1_leftPt_le hT hr t
        have h2 := hC1 t
        calc ‖gW1 T r (leftPt t)‖ * ‖deriv riemannZeta (leftPt t)‖
            ≤ ((|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 1 *
                Real.exp ((1 - t ^ 2) / T ^ 2)) * (C1 * (1 + |t|) ^ N1) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = _ := by rw [pow_add]; ring)
    (integrable_of_poly_gauss ((continuous_gW_leftPt hr).mul continuous_deriv_riemannZeta_leftPt) hT
      (C := r ^ (-1 / 2 : ℝ) * C1) (N := N1) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_gW_leftPt hr]
        have := hC1 t
        calc r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * ‖deriv riemannZeta (leftPt t)‖
            ≤ r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * (C1 * (1 + |t|) ^ N1) := by gcongr
          _ = _ := by ring)
  -- the second
  have h2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t => gW1 T r (leftPt t)) (v := fun t => riemannZeta (leftPt t))
    (u' := fun t => gW2 T r (leftPt t) * I) (v' := fun t => deriv riemannZeta (leftPt t) * I)
    (fun t _ => hg1 t) (fun t _ => hd0 t)
    (integrable_of_poly_gauss ((continuous_gW1_leftPt hr).mul
      (continuous_deriv_riemannZeta_leftPt.mul continuous_const)) hT
      (C := (|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * C1) (N := 1 + N1) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        have h1 := norm_gW1_leftPt_le hT hr t
        have h2 := hC1 t
        calc ‖gW1 T r (leftPt t)‖ * ‖deriv riemannZeta (leftPt t)‖
            ≤ ((|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 1 *
                Real.exp ((1 - t ^ 2) / T ^ 2)) * (C1 * (1 + |t|) ^ N1) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = _ := by rw [pow_add]; ring)
    (integrable_of_poly_gauss (((continuous_gW2_leftPt hr).mul continuous_const).mul
      continuous_riemannZeta_leftPt) hT
      (C := ((|Real.log r| + 2) ^ 2 + 2) * r ^ (-1 / 2 : ℝ) * C0) (N := 2 + 1) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        have h1 := norm_gW2_leftPt_le hT hr t
        have h2 := hC0 t
        calc ‖gW2 T r (leftPt t)‖ * ‖riemannZeta (leftPt t)‖
            ≤ (((|Real.log r| + 2) ^ 2 + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 2 *
                Real.exp ((1 - t ^ 2) / T ^ 2)) * (C0 * (1 + |t|) ^ 1) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = _ := by rw [pow_add]; ring)
    (integrable_of_poly_gauss ((continuous_gW1_leftPt hr).mul continuous_riemannZeta_leftPt) hT
      (C := (|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * C0) (N := 1 + 1) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul]
        have h1 := norm_gW1_leftPt_le hT hr t
        have h2 := hC0 t
        calc ‖gW1 T r (leftPt t)‖ * ‖riemannZeta (leftPt t)‖
            ≤ ((|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 1 *
                Real.exp ((1 - t ^ 2) / T ^ 2)) * (C0 * (1 + |t|) ^ 1) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = _ := by rw [pow_add]; ring)
  -- combine: `I ∫ G ζ'' = −I ∫ G' ζ'` and `I ∫ G' ζ' = −I ∫ G'' ζ`
  have e1 : ∫ t, gW T r (leftPt t) * (deriv (deriv riemannZeta) (leftPt t) * I) =
      I * ∫ t, gW T r (leftPt t) * deriv (deriv riemannZeta) (leftPt t) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have e2 : ∫ t, gW1 T r (leftPt t) * I * deriv riemannZeta (leftPt t) =
      I * ∫ t, gW1 T r (leftPt t) * deriv riemannZeta (leftPt t) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have e3 : ∫ t, gW1 T r (leftPt t) * (deriv riemannZeta (leftPt t) * I) =
      I * ∫ t, gW1 T r (leftPt t) * deriv riemannZeta (leftPt t) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have e4 : ∫ t, gW2 T r (leftPt t) * I * riemannZeta (leftPt t) =
      I * ∫ t, gW2 T r (leftPt t) * riemannZeta (leftPt t) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  have hI : I ≠ 0 := Complex.I_ne_zero
  set A := ∫ t : ℝ, gW T r (leftPt t) * deriv (deriv riemannZeta) (leftPt t) with hA
  set B := ∫ t : ℝ, gW1 T r (leftPt t) * deriv riemannZeta (leftPt t) with hB
  set C := ∫ t : ℝ, gW2 T r (leftPt t) * riemannZeta (leftPt t) with hC
  have h1' : A = -B := mul_left_cancel₀ hI (by rw [h1]; ring)
  have h2' : B = -C := mul_left_cancel₀ hI (by rw [h2]; ring)
  rw [h1', h2', neg_neg]

end

end RHTower.GaussZeroSum
