import GaloisForLFunctions.RHTower.WeilProducerReciprocalZeta
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound

/-!
# Atoms of the boundary measure are the radial orders of the reciprocal zeta function

Let `lam` be full-cone Weil-positive, `μ_lam` the boundary measure of its Herglotz continuation
`Φ_lam`, and `G = 1/F_lam` the continuation to `Re s > 1/2` of
`exp(−Σ_{n≥2} lam(n) n^{−s}/log n)`, the Dirichlet series of the producer's Möbius function.

**Theorem** (`tendsto_log_norm_reciprocalZeta_div_log`).  For every real `a`,

`log ‖G(1/2 + b + ia)‖ / log(1/b) → μ_lam({a})`  as `b → 0⁺`.

So the radial blow-up exponent of the producer's Möbius series at `1/2 + ia` is the boundary
atom: `|G(1/2 + b + ia)| = b^{−μ_lam{a} + o(1)}`.  For `lam = Λ` (a producer exactly under RH) the
atom is the multiplicity of the zero `1/2 + ia` and this is the order of the pole of `1/ζ`.  A
fractional atom gives a fractional radial order.

**Proof.**  Write `G = c (s−1) e^{P}` with `P' = A − Φ_lam` (`exists_reciprocalZeta_primitive`), so
`log ‖G‖ = log ‖c‖ + log ‖s − 1‖ + Re P`.  Along `s = 1/2 + u + ia`, `0 < u ≤ 1/4`, the fundamental
theorem of calculus gives `Re P(1/2+b+ia) = O(1) + ∫_b^{1/4} Re Φ_lam(1/2+u+ia) du`, the archimedean
datum `A` being continuous up to `Re s = 1/2`.  Atom extraction gives `u Re Φ_lam(1/2+u+ia) → μ_lam{a}`
(`tendsto_mul_re_weilContinuation_atom`), and a logarithmic Cesàro lemma
(`tendsto_integral_div_log_of_tendsto_mul`) turns this into `∫_b^{1/4} Re Φ_lam ~ μ_lam{a} log(1/b)`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- **Logarithmic Cesàro lemma.**  If `u h(u) → m` as `u → 0⁺` and `h` is continuous on `(0, c]`,
then `(∫_b^c h) / log(1/b) → m`. -/
theorem tendsto_integral_div_log_of_tendsto_mul {h : ℝ → ℝ} {m c : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn h (Ioc 0 c)) (hlim : Tendsto (fun u => u * h u) (𝓝[>] 0) (𝓝 m)) :
    Tendsto (fun b => (∫ u in b..c, h u) / Real.log (1 / b)) (𝓝[>] 0) (𝓝 m) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim (ε / 2) (by positivity)
  set δ : ℝ := min (δ₀ / 2) (min c (1 / 2)) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (lt_min hc (by norm_num))
  have hδc : δ ≤ c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by norm_num))
  have hδδ₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hint : ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ c → IntervalIntegrable h volume x y :=
    fun x y hx hxy hyc => ContinuousOn.intervalIntegrable_of_Icc hxy
      (hcont.mono fun u hu => ⟨lt_of_lt_of_le hx hu.1, le_trans hu.2 hyc⟩)
  set C : ℝ := |m * Real.log δ| + |∫ u in δ..c, h u| with hCdef
  have hC0 : 0 ≤ C := by positivity
  set η : ℝ := min δ (Real.exp (-(2 * C / ε + 1))) with hηdef
  have hηpos : 0 < η := lt_min hδpos (Real.exp_pos _)
  refine ⟨η, hηpos, fun b hb hbη => ?_⟩
  have hb0 : 0 < b := hb
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hb0] at hbη
  have hbδ : b < δ := lt_of_lt_of_le hbη (min_le_left _ _)
  have hbexp : b < Real.exp (-(2 * C / ε + 1)) := lt_of_lt_of_le hbη (min_le_right _ _)
  set L : ℝ := Real.log (1 / b) with hLdef
  have hLeq : L = -Real.log b := by rw [hLdef, one_div, Real.log_inv]
  have hLbig : 2 * C / ε + 1 < L := by
    rw [hLeq]
    have := Real.log_lt_log hb0 hbexp
    rw [Real.log_exp] at this
    linarith
  have hLpos : 0 < L := by
    have : 0 ≤ 2 * C / ε := by positivity
    linarith
  -- split the integral at `δ`
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint b δ hb0 hbδ.le hδc)
    (hint δ c hδpos hδc le_rfl)
  -- the singular part `∫_b^δ m/u`
  have hlogint : ∫ u in b..δ, m * (1 / u) = m * (Real.log δ + L) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hb0 hδpos,
      Real.log_div hδpos.ne' hb0.ne', hLeq]
    ring
  have hinvint : IntervalIntegrable (fun u : ℝ => m * (1 / u)) volume b δ :=
    ContinuousOn.intervalIntegrable_of_Icc hbδ.le
      (continuousOn_const.mul (continuousOn_const.div continuousOn_id fun u hu =>
        (lt_of_lt_of_le hb0 hu.1).ne'))
  have hεint : IntervalIntegrable (fun u : ℝ => ε / 2 * (1 / u)) volume b δ :=
    ContinuousOn.intervalIntegrable_of_Icc hbδ.le
      (continuousOn_const.mul (continuousOn_const.div continuousOn_id fun u hu =>
        (lt_of_lt_of_le hb0 hu.1).ne'))
  have hdev : |∫ u in b..δ, (h u - m * (1 / u))| ≤ ε / 2 * L := by
    have h1 : ‖∫ u in b..δ, (h u - m * (1 / u))‖ ≤ ∫ u in b..δ, ε / 2 * (1 / u) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hbδ.le
        (Eventually.of_forall fun u hu => ?_) hεint
      have hu0 : 0 < u := lt_trans hb0 hu.1
      have hud : dist u 0 < δ₀ := by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hu0]
        exact lt_of_le_of_lt hu.2 hδδ₀
      have := hδ (show u ∈ Ioi (0 : ℝ) from hu0) hud
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs, show h u - m * (1 / u) = (u * h u - m) / u by field_simp,
        abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
      calc |u * h u - m| ≤ ε / 2 := this.le
        _ = ε / 2 * (1 / u) * u := by field_simp
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hb0 hδpos,
      Real.log_div hδpos.ne' hb0.ne'] at h1
    rw [Real.norm_eq_abs] at h1
    have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδ1
    calc |∫ u in b..δ, (h u - m * (1 / u))| ≤ ε / 2 * (Real.log δ - Real.log b) := h1
      _ ≤ ε / 2 * L := by
          rw [hLeq]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsub := intervalIntegral.integral_sub (hint b δ hb0 hbδ.le hδc) hinvint
  rw [hlogint] at hsub
  -- assemble
  have hmain : |(∫ u in b..c, h u) - m * L| ≤ C + ε / 2 * L := by
    have heq : (∫ u in b..c, h u) - m * L = (∫ u in b..δ, (h u - m * (1 / u))) +
        (m * Real.log δ + ∫ u in δ..c, h u) := by
      rw [← hsplit, hsub]; ring
    rw [heq]
    calc _ ≤ |∫ u in b..δ, (h u - m * (1 / u))| + |m * Real.log δ + ∫ u in δ..c, h u| :=
          abs_add_le _ _
      _ ≤ ε / 2 * L + C := add_le_add hdev (abs_add_le _ _)
      _ = C + ε / 2 * L := by ring
  rw [Real.dist_eq, show (∫ u in b..c, h u) / L - m = ((∫ u in b..c, h u) - m * L) / L by
    field_simp, abs_div, abs_of_pos hLpos, div_lt_iff₀ hLpos]
  have hCL : C < ε / 2 * L := by
    have h2 : 2 * C / ε < L := by linarith
    rw [div_lt_iff₀ hε] at h2
    linarith
  linarith

/-- **Radial order of the reciprocal zeta function of a producer.**  For a full-cone producer
`lam`, the continuation `G` of `1/F_lam = exp(−Σ_{n≥2} lam(n) n^{−s}/log n)` to `Re s > 1/2`
satisfies `log ‖G(1/2 + b + ia)‖ / log(1/b) → μ_lam({a})` as `b → 0⁺`, for every real `a`. -/
theorem tendsto_log_norm_reciprocalZeta_div_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ a : ℝ, Tendsto (fun b : ℝ => Real.log ‖G (((1 / 2 + b : ℝ) : ℂ) + a * I)‖ /
        Real.log (1 / b)) (𝓝[>] 0) (𝓝 ((boundaryMeasure hW).real {a})) := by
  set lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam'
  have hH := herglotzWeilPositive_of_weilPositiveFull hW
  have hAd : DifferentiableOn ℂ zetaArchimedeanDatum {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  have hΦd := differentiableOn_weilContinuation hW
  have hΦid : ∀ s : ℂ, 1 < s.re → weilContinuation hW s =
      zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (fun n => (lam' n : ℂ)) s := by
    intro s hs
    rw [weilContinuation_eq hW hs, weilFunction, zetaArchimedeanDatum]
    rfl
  obtain ⟨c, P, hc0, hPd, hGL⟩ := exists_reciprocalZeta_primitive hH (by simp) hAd hΦd hΦid
  set G : ℂ → ℂ := fun s => c * ((s - 1) * cexp (P s)) with hGdef
  refine ⟨G, fun s hs => ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul
    c).differentiableAt.differentiableWithinAt, hGL, fun a => ?_⟩
  set w₀ : ℂ := (1 / 2 : ℂ) + a * I with hw₀
  have hpt : ∀ b : ℝ, ((1 / 2 + b : ℝ) : ℂ) + a * I = (b : ℂ) + w₀ := fun b => by
    rw [hw₀]; push_cast; ring
  have hre : ∀ u : ℝ, ((u : ℂ) + w₀).re = 1 / 2 + u := fun u => by
    rw [hw₀]; simp; ring
  -- continuity of the archimedean datum on the closed segment
  have hAc : ContinuousOn (fun u : ℝ => (zetaArchimedeanDatum ((u : ℂ) + w₀)).re)
      (Icc 0 (1 / 4)) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine differentiableOn_zetaArchimedeanDatum.continuousOn.comp (by fun_prop) fun u hu => ?_
    show 0 < ((u : ℂ) + w₀).re
    rw [hre]; linarith [hu.1]
  obtain ⟨MA, hMA⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  have hlc : ContinuousOn (fun u : ℝ => Real.log ‖(u : ℂ) + w₀ - 1‖) (Icc 0 (1 / 4)) := by
    refine ContinuousOn.log (by fun_prop) fun u hu => ?_
    rw [norm_ne_zero_iff]
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.sub_re, hre, Complex.one_re, Complex.zero_re] at this
    linarith [hu.2]
  obtain ⟨ML, hML⟩ := isCompact_Icc.exists_bound_of_continuousOn hlc
  -- the main term
  set h : ℝ → ℝ := fun u => (weilContinuation hW ((u : ℂ) + w₀)).re with hhdef
  have hhc : ContinuousOn h (Ioc 0 (1 / 4)) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine hΦd.continuousOn.comp (by fun_prop) fun u hu => ?_
    show 1 / 2 < ((u : ℂ) + w₀).re
    rw [hre]; linarith [hu.1]
  have hhlim : Tendsto (fun u => u * h u) (𝓝[>] 0) (𝓝 ((boundaryMeasure hW).real {a})) := by
    refine (tendsto_mul_re_weilContinuation_atom hW a).congr fun u => ?_
    rw [hhdef, hpt]
  have hmain := tendsto_integral_div_log_of_tendsto_mul (by norm_num : (0 : ℝ) < 1 / 4) hhc hhlim
  -- the bounded remainder
  set B : ℝ → ℝ := fun b => Real.log ‖c‖ + Real.log ‖(b : ℂ) + w₀ - 1‖ +
    (P ((1 / 4 : ℝ) + w₀)).re -
    ∫ u in b..(1 / 4 : ℝ), (zetaArchimedeanDatum ((u : ℂ) + w₀)).re with hBdef
  have hid : ∀ b : ℝ, 0 < b → b ≤ 1 / 4 →
      Real.log ‖G (((1 / 2 + b : ℝ) : ℂ) + a * I)‖ = B b + ∫ u in b..(1 / 4 : ℝ), h u := by
    intro b hb hb4
    rw [hpt]
    have hne : (b : ℂ) + w₀ - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [Complex.sub_re, hre, Complex.one_re, Complex.zero_re] at this
      linarith
    have hnorm : ‖G ((b : ℂ) + w₀)‖ = ‖c‖ * (‖(b : ℂ) + w₀ - 1‖ * Real.exp (P ((b : ℂ) + w₀)).re) := by
      rw [hGdef]; simp only; rw [norm_mul, norm_mul, Complex.norm_exp]
    rw [hnorm, Real.log_mul (norm_ne_zero_iff.mpr hc0)
      (mul_ne_zero (norm_ne_zero_iff.mpr hne) (Real.exp_pos _).ne'),
      Real.log_mul (norm_ne_zero_iff.mpr hne) (Real.exp_pos _).ne', Real.log_exp]
    -- fundamental theorem of calculus for `Re P` along the segment
    have hderiv : ∀ x ∈ uIcc b (1 / 4 : ℝ), HasDerivAt (fun u : ℝ => (P ((u : ℂ) + w₀)).re)
        ((zetaArchimedeanDatum ((x : ℂ) + w₀)).re - h x) x := by
      intro x hx
      rw [uIcc_of_le hb4] at hx
      have hx0 : 1 / 2 < ((x : ℂ) + w₀).re := by rw [hre]; linarith [hx.1]
      have h1 := ((hPd _ hx0).comp_add_const (x : ℂ) w₀).real_of_complex
      rw [Complex.sub_re] at h1
      exact h1
    have hcontA : ContinuousOn (fun u : ℝ => (zetaArchimedeanDatum ((u : ℂ) + w₀)).re)
        (Icc b (1 / 4)) := hAc.mono fun u hu => ⟨le_trans hb.le hu.1, hu.2⟩
    have hcontH : ContinuousOn h (Icc b (1 / 4)) :=
      hhc.mono fun u hu => ⟨lt_of_lt_of_le hb hu.1, hu.2⟩
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hcontA.sub hcontH).intervalIntegrable_of_Icc hb4)
    rw [intervalIntegral.integral_sub (hcontA.intervalIntegrable_of_Icc hb4)
      (hcontH.intervalIntegrable_of_Icc hb4)] at hftc
    rw [hBdef]
    simp only
    push_cast at hftc ⊢
    linarith
  have hBbd : ∀ b : ℝ, 0 < b → b ≤ 1 / 4 →
      |B b| ≤ |Real.log ‖c‖| + ML + |(P ((1 / 4 : ℝ) + w₀)).re| + MA * (1 / 4) := by
    intro b hb hb4
    have h1 : |Real.log ‖(b : ℂ) + w₀ - 1‖| ≤ ML := by
      have := hML b ⟨hb.le, hb4⟩
      rwa [Real.norm_eq_abs] at this
    have h2 : |∫ u in b..(1 / 4 : ℝ), (zetaArchimedeanDatum ((u : ℂ) + w₀)).re| ≤ MA * (1 / 4) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := 1 / 4)
        (C := MA) (f := fun u : ℝ => (zetaArchimedeanDatum ((u : ℂ) + w₀)).re) fun u hu => by
          rw [uIoc_of_le hb4] at hu
          exact hMA u ⟨le_trans hb.le hu.1.le, hu.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - b)] at this
      have hMA0 : 0 ≤ MA := le_trans (norm_nonneg _) (hMA 0 ⟨le_rfl, by norm_num⟩)
      nlinarith
    rw [hBdef]
    simp only
    calc _ ≤ |Real.log ‖c‖ + Real.log ‖(b : ℂ) + w₀ - 1‖ + (P ((1 / 4 : ℝ) + w₀)).re| +
          |∫ u in b..(1 / 4 : ℝ), (zetaArchimedeanDatum ((u : ℂ) + w₀)).re| := abs_sub _ _
      _ ≤ |Real.log ‖c‖| + |Real.log ‖(b : ℂ) + w₀ - 1‖| + |(P ((1 / 4 : ℝ) + w₀)).re| +
          |∫ u in b..(1 / 4 : ℝ), (zetaArchimedeanDatum ((u : ℂ) + w₀)).re| := by
          gcongr
          exact abs_add_three _ _ _
      _ ≤ _ := by linarith
  set M : ℝ := |Real.log ‖c‖| + ML + |(P ((1 / 4 : ℝ) + w₀)).re| + MA * (1 / 4) with hMdef
  have hLtop : Tendsto (fun b : ℝ => Real.log (1 / b)) (𝓝[>] 0) atTop := by
    refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun b => ?_
    simp [one_div, Real.log_inv]
  have hBlim : Tendsto (fun b => B b / Real.log (1 / b)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := M)).div_atTop hLtop)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4),
      hLtop.eventually (eventually_gt_atTop 0)] with b hb hL
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (hBbd b hb.1 hb.2.le) hL.le
  have hsum := hBlim.add hmain
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with b hb
  rw [hid b hb.1 hb.2.le, add_div]

open GaloisForLFunctions.RHTower in
/-- **Quantitative Abel bound.**  If `‖Σ_{n<N} a_n‖ ≤ C (N+1)^α`, then for `Re s > α` the sum of
`Σ a_n (n+1)^{−s}` satisfies `‖Σ a_n (n+1)^{−s}‖ ≤ ‖s‖ C 2^α (1 + 1/(Re s − α))`. -/
theorem norm_dirichletSum_le_of_poly_bounded {a : ℕ → ℂ} {C α : ℝ} (hC0 : 0 ≤ C) (hα : 0 ≤ α)
    (hC : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, a n‖ ≤ C * ((N : ℝ) + 1) ^ α)
    {s : ℂ} (hs : α < s.re) :
    ‖dirichletSum a s‖ ≤ ‖s‖ * (C * (2 : ℝ) ^ α) * (1 + 1 / (s.re - α)) := by
  have hconv : DirichletConvergesAt a s := tendsto_dirichlet_partialSum_of_poly_bounded hC0 hα hC hs
  have htend := tendsto_dirichletSum hconv
  have hspos : 0 < s.re := lt_of_le_of_lt hα hs
  set K : ℝ := ‖s‖ * (C * (2 : ℝ) ^ α) * (1 + 1 / (s.re - α)) with hKdef
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hbdef
  set A : ℕ → ℂ := fun k => ∑ n ∈ Finset.range k, a n with hAdef
  have hincr : ∀ i : ℕ, ‖b (i + 1) - b i‖ ≤ ‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1) := by
    intro i
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hstep := norm_cpow_unit_diff_le hspos hx
    have hb1 : b (i + 1) = ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by
      show (((((i + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = _
      congr 2
      push_cast
      ring
    have hb0 : b i = (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := rfl
    rw [hb1, hb0, norm_sub_rev]
    exact hstep
  have hAbound : ∀ i : ℕ, ‖A (i + 1)‖ ≤ C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α := by
    intro i
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h := hC (i + 1)
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = ((i : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast] at h
    refine le_trans h ?_
    have hmono : (((i : ℝ) + 1) + 1) ^ α ≤ (2 * ((i : ℝ) + 1)) ^ α :=
      Real.rpow_le_rpow (by positivity) (by linarith) hα
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hx.le]
    exact mul_le_mul_of_nonneg_left hmono hC0
  have hterm : ∀ i : ℕ, ‖(b (i + 1) - b i) * A (i + 1)‖ ≤
      ‖s‖ * (C * (2 : ℝ) ^ α) * ((i : ℝ) + 1) ^ (-(s.re + 1 - α)) := by
    intro i
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [norm_mul]
    refine le_trans (mul_le_mul (hincr i) (hAbound i) (norm_nonneg _) (by positivity))
      (le_of_eq ?_)
    rw [show ‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1) * (C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α) =
      ‖s‖ * (C * (2 : ℝ) ^ α) * (((i : ℝ) + 1) ^ (-s.re - 1) * ((i : ℝ) + 1) ^ α) by ring,
      ← Real.rpow_add hx]
    congr 2
    ring
  have hβ : 1 < s.re + 1 - α := by linarith
  have hsumm : Summable fun i : ℕ => ((i : ℝ) + 1) ^ (-(s.re + 1 - α)) :=
    summable_shift_rpow_neg hβ
  have htsum : ∑' i : ℕ, ((i : ℝ) + 1) ^ (-(s.re + 1 - α)) ≤ 1 + 1 / (s.re - α) := by
    have h := tsum_add_one_rpow_le hβ
    rwa [show s.re + 1 - α - 1 = s.re - α by ring] at h
  have habel : ∀ N : ℕ, (∑ n ∈ Finset.range N, a n * b n)
      = b (N - 1) * A N - ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1) := by
    intro N
    have h := Finset.sum_range_by_parts b a N
    simp only [smul_eq_mul] at h
    rw [show (∑ n ∈ Finset.range N, a n * b n) = ∑ n ∈ Finset.range N, b n * a n from
      Finset.sum_congr rfl fun n _ => mul_comm _ _]
    exact h
  have hpart : ∀ N : ℕ, ‖dirichletPartialSum a N s‖ ≤ ‖b (N - 1) * A N‖ + K := by
    intro N
    have heq : dirichletPartialSum a N s = ∑ n ∈ Finset.range N, a n * b n := rfl
    rw [heq, habel N]
    refine le_trans (norm_sub_le _ _) (add_le_add le_rfl ?_)
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
    rw [← Finset.mul_sum, hKdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (hsumm.sum_le_tsum _ fun i _ => by positivity) htsum
  have hTend2 : Tendsto (fun N : ℕ => ‖b (N - 1) * A N‖) atTop (𝓝 0) := by
    have hmajT : Tendsto (fun N : ℕ => (C * (2 : ℝ) ^ α) * ((N : ℝ)) ^ (-(s.re - α)))
        atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_nat_atTop (show (0 : ℝ) < s.re - α by linarith)).const_mul
        (C * (2 : ℝ) ^ α)
      simpa using h
    refine squeeze_zero_norm' ?_ hmajT
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_norm]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      rw [Nat.cast_sub hN]; push_cast; ring
    have hbnorm : ‖b (N - 1)‖ = (N : ℝ) ^ (-s.re) := by
      simp only [hbdef]
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      rfl
    have hAn : ‖A N‖ ≤ C * (2 : ℝ) ^ α * (N : ℝ) ^ α := by
      refine le_trans (hC N) ?_
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hmono : ((N : ℝ) + 1) ^ α ≤ (2 * (N : ℝ)) ^ α :=
        Real.rpow_le_rpow (by positivity) (by linarith) hα
      rw [mul_assoc, ← Real.mul_rpow (by norm_num) hNpos.le]
      exact mul_le_mul_of_nonneg_left hmono hC0
    rw [norm_mul, hbnorm]
    refine le_trans (mul_le_mul_of_nonneg_left hAn (Real.rpow_nonneg hNpos.le _)) (le_of_eq ?_)
    rw [show (N : ℝ) ^ (-s.re) * (C * (2 : ℝ) ^ α * (N : ℝ) ^ α)
        = (C * (2 : ℝ) ^ α) * ((N : ℝ) ^ (-s.re) * (N : ℝ) ^ α) by ring,
      ← Real.rpow_add hNpos]
    congr 2
    ring
  have hlim := hTend2.add_const K
  rw [zero_add] at hlim
  exact le_of_tendsto_of_tendsto htend.norm hlim (Eventually.of_forall hpart)

open GaloisForLFunctions.RHTower in
/-- **Square-root Möbius bounds force atoms of mass at most one.**  Let `lam` be a full-cone
producer and `M(N) = Σ_{1≤m≤N} μ_lam(m)` the Mertens function of its Möbius function (the
Dirichlet coefficients of `1/F_lam`).  If `|M(N)| ≤ C √(N+1)` for all `N`, then every atom of the
boundary measure has mass `μ_lam({a}) ≤ 1`.  For `lam = Λ` this is the statement that
`M(x) = O(√x)` forces all critical zeros to be simple. -/
theorem boundaryMeasure_real_singleton_le_one_of_mertens {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ} (hC : ∀ N : ℕ, ‖∑ n ∈ Finset.range N,
      producerMobius (fun n => if 2 ≤ n then lam n else 0) (n + 1)‖ ≤
        C * ((N : ℝ) + 1) ^ (1 / 2 : ℝ)) (a : ℝ) :
    (boundaryMeasure hW).real {a} ≤ 1 := by
  set lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam'
  set c : ℕ → ℂ := fun n => producerMobius lam' (n + 1) with hcdef
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'0 : 0 ≤ C' := by linarith
  have hC' : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, c n‖ ≤ C' * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) :=
    fun N => le_trans (hC N) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨G, hGd, hGL, hrad⟩ := tendsto_log_norm_reciprocalZeta_div_log hW
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hconv : ∀ s ∈ U, DirichletConvergesAt c s := fun s hs =>
    tendsto_dirichlet_partialSum_of_poly_bounded hC'0 (by norm_num) hC' hs
  have hDd : DifferentiableOn ℂ (dirichletSum c) U := by
    intro s hs
    have hs' : (1 / 2 : ℝ) < s.re := hs
    set s₀ : ℂ := (((1 / 2 + s.re) / 2 : ℝ) : ℂ) with hs₀
    have hs₀U : s₀ ∈ U := by
      show (1 / 2 : ℝ) < s₀.re
      rw [hs₀, Complex.ofReal_re]; linarith
    have hlt : s₀.re < s.re := by rw [hs₀, Complex.ofReal_re]; linarith
    have hopen : IsOpen {z : ℂ | s₀.re < z.re} := isOpen_lt continuous_const Complex.continuous_re
    exact ((differentiableOn_dirichletSum (hconv s₀ hs₀U)).differentiableAt
      (hopen.mem_nhds hlt)).differentiableWithinAt
  -- on `Re s > 1` the Dirichlet sum is `1/F_lam`
  have hagreeR : ∀ s : ℂ, 1 < s.re → dirichletSum c s = G s := by
    intro s hs
    have hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam' n| / (n : ℝ) ^ σ :=
      (herglotzWeilPositive_of_weilPositiveFull hW).summable
    obtain ⟨hLS, hLeq⟩ := LSeries_producerMobius hsum hs
    have hhas : HasSum (LSeries.term (producerMobius lam') s) (LSeries (producerMobius lam') s) :=
      hLS.LSeriesHasSum
    have hhas' : HasSum (fun n => LSeries.term (producerMobius lam') s (n + 1))
        (LSeries (producerMobius lam') s) := by
      have := (hasSum_nat_add_iff' 1).mpr hhas
      simpa [LSeries.term_zero] using this
    have htend : Tendsto (fun N => dirichletPartialSum c N s) atTop
        (𝓝 (LSeries (producerMobius lam') s)) := by
      refine hhas'.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => ?_
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
      simp only [hcdef]
      push_cast
      ring
    rw [tendsto_nhds_unique (tendsto_dirichletSum ⟨_, htend⟩) htend, hLeq, hGL s hs]
  have hagree : EqOn (dirichletSum c) G U := by
    have h2U : (2 : ℂ) ∈ U := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
    refine (hDd.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
      (hGd.analyticOnNhd hUopen) hUconn h2U ?_
    have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hagreeR z hz
  -- the radial upper bound
  set z : ℝ → ℂ := fun b => (((1 / 2 + b : ℝ) : ℂ) + a * I) with hzdef
  have hzre : ∀ b : ℝ, (z b).re = 1 / 2 + b := fun b => by simp [hzdef]
  set R : ℝ → ℝ := fun b => Real.log (‖z b‖ * (C' * (2 : ℝ) ^ (1 / 2 : ℝ))) + Real.log (1 + b)
    with hRdef
  have hbound : ∀ b : ℝ, 0 < b → b ≤ 1 / 4 →
      Real.log ‖G (z b)‖ / Real.log (1 / b) ≤ 1 + R b / Real.log (1 / b) := by
    intro b hb hb4
    have hzU : z b ∈ U := by show (1 / 2 : ℝ) < (z b).re; rw [hzre]; linarith
    have hD := norm_dirichletSum_le_of_poly_bounded hC'0 (by norm_num) hC'
      (show (1 / 2 : ℝ) < (z b).re by rw [hzre]; linarith)
    rw [hagree hzU, hzre, show 1 / 2 + b - 1 / 2 = b by ring] at hD
    have hzpos : 0 < ‖z b‖ := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1 / 2 + b)
      ((hzre b).symm ▸ Complex.re_le_norm (z b))
    have hK0 : 0 < C' * (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hsplit : ‖z b‖ * (C' * (2 : ℝ) ^ (1 / 2 : ℝ)) * (1 + 1 / b) =
        ‖z b‖ * (C' * (2 : ℝ) ^ (1 / 2 : ℝ)) * (1 + b) * (1 / b) := by field_simp; ring
    have hLpos : 0 < Real.log (1 / b) := Real.log_pos (by rw [lt_div_iff₀ hb]; linarith)
    have hlogK : Real.log (‖z b‖ * (C' * (2 : ℝ) ^ (1 / 2 : ℝ)) * (1 + 1 / b)) =
        R b + Real.log (1 / b) := by
      rw [hsplit, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), hRdef]
    have hle : Real.log ‖G (z b)‖ ≤ R b + Real.log (1 / b) := by
      rw [← hlogK]
      rcases (norm_nonneg (G (z b))).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        refine Real.log_nonneg ?_
        have h1 : (1 : ℝ) ≤ ‖z b‖ * 2 := by
          have := (hzre b).symm ▸ Complex.re_le_norm (z b)
          linarith
        have h2 : (1 : ℝ) ≤ C' * (2 : ℝ) ^ (1 / 2 : ℝ) :=
          one_le_mul_of_one_le_of_one_le hC'1 (Real.one_le_rpow (by norm_num) (by norm_num))
        have h3 : (2 : ℝ) ≤ 1 + 1 / b := by
          have : (4 : ℝ) ≤ 1 / b := by rw [le_div_iff₀ hb]; linarith
          linarith
        calc (1 : ℝ) ≤ ‖z b‖ * 2 * 1 := by linarith
          _ ≤ ‖z b‖ * (C' * (2 : ℝ) ^ (1 / 2 : ℝ)) * (1 + 1 / b) := by
              rw [show ‖z b‖ * 2 * 1 = ‖z b‖ * 1 * 2 by ring]
              exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) h3 (by norm_num)
                (by positivity)
      · exact Real.log_le_log hpos (hD.trans (le_of_eq (by ring)))
    rw [div_le_iff₀ hLpos, add_mul, one_mul, div_mul_cancel₀ _ hLpos.ne']
    linarith
  have hLtop : Tendsto (fun b : ℝ => Real.log (1 / b)) (𝓝[>] 0) atTop := by
    refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun b => ?_
    simp [one_div, Real.log_inv]
  have hRc : ContinuousAt R 0 := by
    have hz0 : 0 < ‖z 0‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (by have := Complex.re_le_norm (z 0); rw [hzre] at this; linarith)
    refine ContinuousAt.add ?_ ?_
    · refine ContinuousAt.log (by fun_prop) ?_
      positivity
    · exact ContinuousAt.log (by fun_prop) (by norm_num)
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := hRc.tendsto.mono_left nhdsWithin_le_nhds
  have hrhs : Tendsto (fun b => 1 + R b / Real.log (1 / b)) (𝓝[>] 0) (𝓝 1) := by
    have := (hRlim.div_atTop hLtop).const_add 1
    rwa [add_zero] at this
  refine le_of_tendsto_of_tendsto (hrad a) hrhs ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with b hb
  exact hbound b hb.1 hb.2.le

end RHTower.WeilSpectral

end
