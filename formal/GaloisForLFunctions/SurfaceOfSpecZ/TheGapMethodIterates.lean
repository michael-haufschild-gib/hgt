import GaloisForLFunctions.SurfaceOfSpecZ.AlmostAllPrimesSuffice

/-!
# The gap method iterates

`HasseWeilAtThePrimeDegreesBoundsTheWidth` transfers a lower bound at a degree set with gaps `x^θ`
to all `u` using the a priori Lipschitz constant `e^{u/2}` of the lag structure, and obtains width
`≤ θ − ½`. The Lipschitz constant improves with the width: if every zero has `Re ρ ≤ ½ + a`, then
`|S(t) − S(s)| ≤ L (t − s) e^{at}` (`norm_lagStructure_sub_le_of_width`). One step then gives width
`≤ max(β₀, a + θ − 1)` (`width_step_of_powGaps`), `β₀` the depth of the deepest real zero, and the
steps lower the width by `1 − θ` until it reaches `β₀`.

**Theorem** (`re_le_of_bddBelow_of_powGaps_of_realDepth`). Let `Z` be a tempered configuration whose real zeros have
`Re ρ ≤ ½ + β₀`, `0 ≤ β₀ < ½`, and `D` a degree set with gaps `O(x^θ)`, `θ < 1`. If
`2 Re S_Z(log d) ≥ −K` for `d ∈ D`, every zero has `Re ρ ≤ ½ + β₀`.

No attained maximum, no Dirichlet series and no sampling are used, only gaps with a power saving.
Hence for every configuration without real zeros a lower bound at the primes (Huxley's gaps
`x^{2/3}`), at the `pᵏ` (gaps `x^{1 − 1/(3k)}`), or at any degree set with power-saving gaps puts
every zero on the line (`onLine_of_bddBelow_of_powGaps`, `onLine_of_bddBelow_primes`,
`onLine_of_bddBelow_kthPrimePowers`); for `L(s, χ)` a lower bound at the primes puts every zero at
or left of the deepest real zero (`re_le_of_bddBelow_primes_L`). The critical gap exponent `½` of the
one-step method is not a barrier.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- `‖e^{zt} − e^{zs}‖ ≤ ‖z‖ (t − s) e^{at}` when `Re z ≤ a`, `a ≥ 0`, `0 ≤ s ≤ t`. -/
theorem norm_cexp_sub_le_of_re_le {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (hz : z.re ≤ a) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖cexp (z * t) - cexp (z * s)‖ ≤ ‖z‖ * (t - s) * Real.exp (a * t) := by
  have hderiv : ∀ τ ∈ Set.Icc s t, HasDerivWithinAt (fun τ : ℝ => cexp (z * τ))
      (z * cexp (z * τ)) (Set.Icc s t) τ := by
    intro τ _
    have h1 : HasDerivAt (fun τ : ℝ => z * (τ : ℂ)) (z * 1) τ :=
      ((hasDerivAt_id τ).ofReal_comp).const_mul z
    have h2 := h1.cexp
    simpa [mul_comm] using h2.hasDerivWithinAt
  have hbound : ∀ τ ∈ Set.Ico s t, ‖z * cexp (z * τ)‖ ≤ ‖z‖ * Real.exp (a * t) := by
    intro τ hτ
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (z * (τ : ℂ)).re = z.re * τ := by simp
    rw [this]
    have hτ0 : 0 ≤ τ := hs.trans hτ.1
    calc z.re * τ ≤ a * τ := mul_le_mul_of_nonneg_right hz hτ0
      _ ≤ a * t := mul_le_mul_of_nonneg_left hτ.2.le ha
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨hst, le_rfl⟩
  calc ‖cexp (z * t) - cexp (z * s)‖ ≤ ‖z‖ * Real.exp (a * t) * (t - s) := this
    _ = ‖z‖ * (t - s) * Real.exp (a * t) := by ring

/-- **At width `a` the lag structure is Lipschitz with constant `L e^{at}`.** -/
theorem norm_lagStructure_sub_le_of_width {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {a : ℝ}
    (ha : 0 ≤ a) (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    ‖lagStructure Z b t - lagStructure Z b s‖ ≤
      (∑' z : ℂ, ‖lagCoeff Z b z‖ * ‖z‖) * (t - s) * Real.exp (a * t) := by
  obtain ⟨hst1, hst2⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs t
  obtain ⟨hss1, hss2⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs s
  have hL := summable_norm_lagCoeff_mul_norm hZ hb hw hbs
  have hterm : ∀ z : ℂ, ‖lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s)‖ ≤
      ‖lagCoeff Z b z‖ * ‖z‖ * ((t - s) * Real.exp (a * t)) := by
    intro z
    by_cases hF : lagCoeff Z b z = 0
    · simp [hF]
    have hmem : (1 / 2 + z) ∈ Z.carrier := by
      by_contra h; exact hF (by rw [lagCoeff, Set.indicator_of_notMem h])
    have hre : z.re ≤ a := by have := hwid _ hmem; simp at this; linarith
    rw [← mul_sub, norm_mul]
    have := norm_cexp_sub_le_of_re_le ha hre hs hst
    calc ‖lagCoeff Z b z‖ * ‖cexp (z * t) - cexp (z * s)‖
        ≤ ‖lagCoeff Z b z‖ * (‖z‖ * (t - s) * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  have hsum : Summable fun z : ℂ => ‖lagCoeff Z b z‖ * ‖z‖ * ((t - s) * Real.exp (a * t)) :=
    hL.mul_right _
  have hsum' : Summable fun z : ℂ =>
      ‖lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum
  rw [hst2, hss2, ← hst1.tsum_sub hss1]
  calc ‖∑' z, (lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s))‖
      ≤ ∑' z, ‖lagCoeff Z b z * cexp (z * t) - lagCoeff Z b z * cexp (z * s)‖ :=
        norm_tsum_le_tsum_norm hsum'
    _ ≤ ∑' z, ‖lagCoeff Z b z‖ * ‖z‖ * ((t - s) * Real.exp (a * t)) :=
        Summable.tsum_le_tsum hterm hsum' hsum
    _ = _ := by rw [tsum_mul_right]; ring

/-- At width `a` the spline traces are Lipschitz with constant `2L e^{at}`. -/
theorem abs_two_re_lagStructure_sub_le_of_width {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (ha0 : 0 ≤ a) (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    |2 * (lagStructure Z (boxSpline 1 3) t).re - 2 * (lagStructure Z (boxSpline 1 3) s).re| ≤
      2 * (∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖) * (t - s) * Real.exp (a * t) := by
  have hb : ContDiff ℝ 2 (boxSpline 1 3) := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hw : (0 : ℝ) ≤ ((3 : ℕ) + 1) * 1 := by positivity
  have h := norm_lagStructure_sub_le_of_width hZ hb hw hbs ha0 hwid hs hst
  have hre := Complex.abs_re_le_norm
    (lagStructure Z (boxSpline 1 3) t - lagStructure Z (boxSpline 1 3) s)
  rw [Complex.sub_re] at hre
  have heq : |2 * (lagStructure Z (boxSpline 1 3) t).re -
      2 * (lagStructure Z (boxSpline 1 3) s).re| =
      2 * |(lagStructure Z (boxSpline 1 3) t).re - (lagStructure Z (boxSpline 1 3) s).re| := by
    rw [← mul_sub, abs_mul]; norm_num
  rw [heq]
  linarith

/-- Near every large `u` a degree `d ∈ D` has `0 ≤ log d ≤ u ≤ log d + 2M e^{(θ−1)u}`. -/
theorem exists_log_degree_near {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) :
    ∃ M T₀ : ℝ, 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ u : ℝ, T₀ ≤ u → ∃ d ∈ D, 0 ≤ Real.log d ∧
      Real.log d ≤ u ∧ u - Real.log d ≤ 2 * M * Real.exp ((θ - 1) * u) := by
  obtain ⟨hpos, M, X, hM0, hgapD⟩ := hD
  set T₀ : ℝ := max (max (Real.log (max X 1)) (Real.log (2 * M + 1) / (1 - θ))) 0 with hT₀
  refine ⟨M, T₀, hM0, le_max_right _ _, fun u hu => ?_⟩
  have hxX : X ≤ Real.exp u := by
    have h1 : Real.log (max X 1) ≤ u := (le_max_left _ _).trans ((le_max_left _ _).trans hu)
    have h2 : max X 1 ≤ Real.exp u := by
      rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right X 1))]
      exact Real.exp_le_exp.mpr h1
    exact (le_max_left _ _).trans h2
  obtain ⟨d, hdD, hdle, hdgap⟩ := hgapD (Real.exp u) hxX
  rw [← Real.exp_mul, mul_comm u θ] at hdgap
  have hsmall : M * Real.exp (θ * u) ≤ Real.exp u / 2 := by
    have h1 : Real.log (2 * M + 1) / (1 - θ) ≤ u :=
      (le_max_right _ _).trans ((le_max_left _ _).trans hu)
    have h2 : Real.log (2 * M + 1) ≤ (1 - θ) * u := by
      rw [div_le_iff₀ (by linarith)] at h1; linarith
    have h3 : 2 * M + 1 ≤ Real.exp ((1 - θ) * u) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < 2 * M + 1)]; exact Real.exp_le_exp.mpr h2
    have h4 : Real.exp u = Real.exp ((1 - θ) * u) * Real.exp (θ * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [h4]
    have := Real.exp_pos (θ * u)
    nlinarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hpos d hdD
  have hd0 : (0 : ℝ) < d := by linarith
  refine ⟨d, hdD, Real.log_nonneg hd1, by rw [← Real.log_exp u]; exact Real.log_le_log hd0 hdle,
    ?_⟩
  have h1 : u - Real.log d = Real.log (Real.exp u / d) := by
    rw [Real.log_div (Real.exp_pos u).ne' hd0.ne', Real.log_exp]
  have h2 := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos u) hd0)
  have h3 : Real.exp u / d - 1 = (Real.exp u - d) / d := by field_simp
  have hMe : 0 ≤ M * Real.exp (θ * u) := mul_nonneg hM0 (Real.exp_pos _).le
  have h4 : (Real.exp u - d) / d ≤ M * Real.exp (θ * u) * (2 / Real.exp u) := by
    rw [div_le_iff₀ hd0]
    have h5 : 1 ≤ 2 / Real.exp u * d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos u)]; linarith
    nlinarith
  have h5 : M * Real.exp (θ * u) * (2 / Real.exp u) = 2 * M * Real.exp ((θ - 1) * u) := by
    rw [show (θ - 1) * u = θ * u - u by ring, Real.exp_sub]; ring
  linarith

/-- **Transfer from a gap set.** At width `a`, the trace at every large `u` is within
`C e^{(a + θ − 1)u}` of the trace at a degree of `D`. -/
theorem exists_degree_trace_near {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ} (ha0 : 0 ≤ a)
    (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 0 ≤ T₀ ∧ ∀ u : ℝ, T₀ ≤ u → ∃ d ∈ D,
      |2 * (lagStructure Z (boxSpline 1 3) u).re -
        2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re| ≤
          C * Real.exp ((a + θ - 1) * u) := by
  obtain ⟨M, T₀, hM0, hT₀0, hnear⟩ := exists_log_degree_near hθ1 hD
  set L := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hLdef
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  refine ⟨4 * L * M, T₀, by positivity, hT₀0, fun u hu => ?_⟩
  obtain ⟨d, hdD, hlogd0, hlogd, hgap⟩ := hnear u hu
  refine ⟨d, hdD, ?_⟩
  have hl := abs_two_re_lagStructure_sub_le_of_width hZ ha0 hwid hlogd0 hlogd
  have h2L : 0 ≤ 2 * L := by linarith
  have h1 : 2 * L * (u - Real.log d) * Real.exp (a * u) ≤
      2 * L * (2 * M * Real.exp ((θ - 1) * u)) * Real.exp (a * u) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap h2L) (Real.exp_pos _).le
  have h2 : Real.exp ((θ - 1) * u) * Real.exp (a * u) = Real.exp ((a + θ - 1) * u) := by
    rw [← Real.exp_add]; ring_nf
  calc _ ≤ 2 * L * (u - Real.log d) * Real.exp (a * u) := hl
    _ ≤ 2 * L * (2 * M * Real.exp ((θ - 1) * u)) * Real.exp (a * u) := h1
    _ = 4 * L * M * (Real.exp ((θ - 1) * u) * Real.exp (a * u)) := by ring
    _ = 4 * L * M * Real.exp ((a + θ - 1) * u) := by rw [h2]

/-- **One step of the gap method.** A lower bound at a degree set with gaps `O(x^θ)`, at width `a`,
gives width `max(β₀, a + θ − 1)`. -/
theorem width_step_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z) {β₀ : ℝ} (hβ₀0 : 0 ≤ β₀)
    (hβ₀ : β₀ < 1 / 2) (hreal0 : ∀ ρ ∈ Z.carrier, ρ.im = 0 → ρ.re ≤ 1 / 2 + β₀) {θ a : ℝ}
    (hθ1 : θ < 1) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    {D : Set ℕ} (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + max β₀ (a + θ - 1) := by
  have hb : ContDiff ℝ 2 (boxSpline 1 3) := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  set a' := max β₀ (a + θ - 1) with ha'
  have ha'0 : 0 ≤ a' := hβ₀0.trans (le_max_left _ _)
  have ha'1 : a' < 1 / 2 := max_lt hβ₀ (by linarith)
  obtain ⟨C, T₀, hC0, hT₀0, htrans⟩ := exists_degree_trace_near hZ ha0 hwid hθ1 hD
  -- far from `0`, through the nearest degree
  have hfar : ∀ u : ℝ, T₀ ≤ u →
      -((|K| + C) * Real.exp (a' * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
    intro u hu
    have hu0 : 0 ≤ u := hT₀0.trans hu
    obtain ⟨d, hdD, hvar⟩ := htrans u hu
    have he : Real.exp ((a + θ - 1) * u) ≤ Real.exp (a' * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu0)
    have hvar' := (abs_le.mp hvar).1
    have hCe := mul_le_mul_of_nonneg_left he hC0
    have hone : 1 ≤ Real.exp (a' * u) := Real.one_le_exp (by positivity)
    have hKe : K ≤ |K| * Real.exp (a' * u) := by nlinarith [le_abs_self K, abs_nonneg K]
    linarith [hK d hdD]
  -- near `0`, through `u = 0`
  set L := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hLdef
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  set C₀ := |2 * (lagStructure Z (boxSpline 1 3) 0).re| + 2 * L * T₀ * Real.exp (a * T₀) with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]; have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L) hT₀0)
      (Real.exp_pos (a * T₀)).le
    positivity
  have hnear : ∀ u : ℝ, 0 ≤ u → u ≤ T₀ → -C₀ ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
    intro u hu huT
    have h := abs_two_re_lagStructure_sub_le_of_width hZ ha0 hwid le_rfl hu
    have h2L : 0 ≤ 2 * L := by linarith
    have he : Real.exp (a * u) ≤ Real.exp (a * T₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huT ha0)
    have hA : 2 * L * (u - 0) ≤ 2 * L * T₀ := mul_le_mul_of_nonneg_left (by linarith) h2L
    have h1 : 2 * L * (u - 0) * Real.exp (a * u) ≤ 2 * L * T₀ * Real.exp (a * T₀) :=
      calc 2 * L * (u - 0) * Real.exp (a * u) ≤ 2 * L * T₀ * Real.exp (a * u) :=
            mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
        _ ≤ 2 * L * T₀ * Real.exp (a * T₀) :=
            mul_le_mul_of_nonneg_left he (mul_nonneg h2L hT₀0)
    have := (abs_le.mp h).1
    linarith [neg_abs_le (2 * (lagStructure Z (boxSpline 1 3) 0).re)]
  -- a lower bound `−M' e^{a'u}` on `u ≥ 0`
  set M' := |K| + C + C₀ with hM'
  have hMa : ∀ u : ℝ, 0 ≤ u →
      -(M' * Real.exp (a' * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
    intro u hu
    have hone : 1 ≤ Real.exp (a' * u) := Real.one_le_exp (by positivity)
    have he0 : 0 ≤ Real.exp (a' * u) := (Real.exp_pos _).le
    rcases le_total T₀ u with hTu | huT
    · have := hfar u hTu
      have : 0 ≤ C₀ * Real.exp (a' * u) := mul_nonneg hC₀0 he0
      nlinarith
    · have := hnear u hu huT
      have : C₀ ≤ C₀ * Real.exp (a' * u) := le_mul_of_one_le_right hC₀0 hone
      have : 0 ≤ (|K| + C) * Real.exp (a' * u) := mul_nonneg (by positivity) he0
      nlinarith
  -- real exponents lie at depth `≤ β₀`
  have hreal : ∀ x : ℂ, evenCoeff Z (boxSpline 1 3) x ≠ 0 → x.im = 0 → x.re ≤ a' := by
    intro x hx him
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · have := hreal0 _ h (by simp [him]); simp at this; linarith [le_max_left β₀ (a + θ - 1)]
    · have := hreal0 _ h (by simp [him]); simp at this; linarith [le_max_left β₀ (a + θ - 1)]
  intro ρ hρ
  by_contra hlt
  push Not at hlt
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  exact hz₀ (evenCoeff_eq_zero_of_two_re_lagStructure_ge Z hZ hb hbs ha'0 ha'1 hreal hMa
    (by simp; linarith))

/-- **The gap method iterates.** For a tempered configuration whose real zeros have
`Re ρ ≤ ½ + β₀`, `0 ≤ β₀ < ½`, a lower bound at a degree set with power-saving gaps puts every zero
at `Re ρ ≤ ½ + β₀`. -/
theorem re_le_of_bddBelow_of_powGaps_of_realDepth (Z : ZeroConfig) (hZ : TemperedConfig Z) {β₀ : ℝ}
    (hβ₀0 : 0 ≤ β₀) (hβ₀ : β₀ < 1 / 2) (hreal0 : ∀ ρ ∈ Z.carrier, ρ.im = 0 → ρ.re ≤ 1 / 2 + β₀)
    {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + β₀ := by
  have hstep : ∀ n : ℕ, ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + max β₀ (1 / 2 - n * (1 - θ)) := by
    intro n
    induction n with
    | zero =>
      intro ρ hρ
      have h1 : ρ.re ≤ 1 := by have := (Z.strip ρ hρ).2; simpa using this
      have : max β₀ (1 / 2 - ((0 : ℕ) : ℝ) * (1 - θ)) = 1 / 2 := by
        rw [Nat.cast_zero, zero_mul, sub_zero, max_eq_right hβ₀.le]
      rw [this]; linarith
    | succ n ih =>
      have ha0 : 0 ≤ max β₀ (1 / 2 - n * (1 - θ)) := hβ₀0.trans (le_max_left _ _)
      have ha : max β₀ (1 / 2 - n * (1 - θ)) ≤ 1 / 2 :=
        max_le hβ₀.le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      have h := width_step_of_powGaps Z hZ hβ₀0 hβ₀ hreal0 hθ1 ha0 ha ih hD hK
      have hnew : max β₀ (max β₀ (1 / 2 - n * (1 - θ)) + θ - 1) ≤
          max β₀ (1 / 2 - ((n + 1 : ℕ) : ℝ) * (1 - θ)) := by
        push_cast
        apply max_le (le_max_left _ _)
        rcases le_total β₀ (1 / 2 - n * (1 - θ)) with h0 | h0
        · rw [max_eq_right h0]; exact le_max_of_le_right (by linarith)
        · rw [max_eq_left h0]; exact le_max_of_le_left (by linarith)
      intro ρ hρ
      linarith [h ρ hρ]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * (1 - θ)))
  have hθ0 : 0 < 1 - θ := by linarith
  have hn' : 1 / 2 - n * (1 - θ) ≤ β₀ := by
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  intro ρ hρ
  have := hstep n ρ hρ
  rw [max_eq_left hn'] at this
  exact this

/-- **Without real zeros, every degree set with power-saving gaps decides the line.** -/
theorem onLine_of_bddBelow_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D)
    {K : ℝ} (hK : ∀ d ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have h := re_le_of_bddBelow_of_powGaps_of_realDepth Z hZ le_rfl (by norm_num)
    (fun ρ hρ him => absurd him (hnoreal ρ hρ)) hθ1 hD hK
  intro ρ hρ
  have h1 := h ρ hρ
  have h2 := h _ (Z.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  rw [hrefl] at h2
  linarith

/-- **The primes decide the line for every configuration without real zeros**, with no attained
maximum: Huxley's gaps `x^{2/3}` and two steps of the gap method. -/
theorem onLine_of_bddBelow_primes (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_of_powGaps Z hZ hnoreal (θ := 2 / 3) (by norm_num)
    (powGaps_primes (by norm_num) (by norm_num)) fun d hd => hK d hd

/-- **The `k`-th prime powers decide the line for every configuration without real zeros.** -/
theorem onLine_of_bddBelow_kthPrimePowers (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {k : ℕ} (hk : 1 ≤ k) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (k * Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hk0 : (0 : ℝ) < 3 * k := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                   linarith
  refine onLine_of_bddBelow_of_powGaps Z hZ hnoreal (θ := 1 - 1 / (3 * k)) (K := K)
    (by have := one_div_pos.mpr hk0; linarith) (powGaps_kthPrimePowers hk) ?_
  rintro d ⟨p, hp, rfl⟩
  have := hK p hp
  rwa [Nat.cast_pow, Real.log_pow]

/-- **For `L(s, χ)` the primes see every zero above the deepest real zero.** If every real zero of
`L(s, χ)` has `Re ρ ≤ ½ + β₀`, `0 ≤ β₀ < ½`, a lower bound on the spline traces of its zeros at the
primes puts every zero at `Re ρ ≤ ½ + β₀`. -/
theorem re_le_of_bddBelow_primes_L {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 1 < q)
    (hprim : χ.IsPrimitive) {β₀ : ℝ} (hβ₀0 : 0 ≤ β₀) (hβ₀ : β₀ < 1 / 2)
    (hreal0 : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.im = 0 → ρ.re ≤ 1 / 2 + β₀)
    {K : ℝ} (hK : ∀ p : ℕ, p.Prime →
      -K ≤ 2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hq hprim)) (boxSpline 1 3)
        (Real.log p)).re) :
    ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re ≤ 1 / 2 + β₀ :=
  re_le_of_bddBelow_of_powGaps_of_realDepth _ (temperedConfig_LZeros hq hprim) hβ₀0 hβ₀ hreal0 (θ := 2 / 3)
    (by norm_num) (powGaps_primes (by norm_num) (by norm_num)) fun d hd => hK d hd

end GaloisForLFunctions.SurfaceOfSpecZ
