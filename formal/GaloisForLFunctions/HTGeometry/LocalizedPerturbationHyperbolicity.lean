import GaloisForLFunctions.HTGeometry.HyperbolicCriticalAlternation

/-!
# The localized `C¹` perturbation lemma for hyperbolicity

A hyperbolic real polynomial `C` with simple critical points and nonvanishing critical values stays
hyperbolic under a deformation `D` whose **value** and **slope** are small on curvature windows
around the critical points.  This is the general-`t` (even-free) positivity engine of the
Jensen-section assembly: the sign transfer no longer needs the symmetric base point.

The window data is total, in the sense of the card's `(D1)`–`(D3)`: around every simple critical
point there is a closed window on which `|C''|` is bounded below by a positive constant and keeps
its sign (`exists_curvature_window`, by continuity — no inflection-distance bookkeeping and no
`N = 2` special case), and the windows can be taken pairwise disjoint
(`exists_perturbation_windows`).  The degenerate case of the card's `(W1)` — a perturbation whose
slope vanishes on a window, so that the displacement radius is `0` — is covered: the critical point
simply does not move.

The `s`-derivative estimates are the quantitative Rolle/IVT chain:

* `abs_eval_sub_le_of_abs_second_derivative_bound` — the second-order Taylor bound
  `|C(t) − C(c)| ≤ M (t−c)²/2` at a critical point, proved by monotonicity of the comparison
  function rather than by an integral remainder;
* `exists_perturbed_critical_point` — `|C'(c ± ε)| ≥ m ε ≥ sup|D'|` on the window forces
  `F' = C' + D'` to keep the sign of `C'` at the two window endpoints, so `F'` has a root within
  `ε = e/m` of `c`;
* `hyperbolic_of_localized_perturbation` — the sign of `C` at each critical point survives, the
  critical values alternate (`HyperbolicCriticalAlternation`), the two outer sign changes come from
  the preserved leading coefficient, and `hyperbolic_of_sign_changes` closes the count.

## Main results

* `hyperbolic_of_localized_perturbation` — the card's `§1⁗` lemma, with hypotheses `(b_i′)` and
  `(a_i″)`;
* `exists_perturbation_windows` — the window data `(D1)`–`(D3)` always exists;
* `exists_perturbed_critical_point`, `abs_eval_sub_le_of_abs_second_derivative_bound` — the two
  reusable quantitative steps.
-/

namespace GaloisForLFunctions.SignAlternation

open Polynomial Set Filter

/-! ### A second-order Taylor bound at a critical point -/

private theorem eval_sub_le_aux {p : ℝ[X]} {c M r : ℝ}
    (hp' : p.derivative.eval c = 0)
    (hM : ∀ s ∈ Icc (c - r) (c + r), p.derivative.derivative.eval s ≤ M)
    {t : ℝ} (ht : t ∈ Icc (c - r) (c + r)) :
    p.eval t - p.eval c ≤ M * (t - c) ^ 2 / 2 := by
  have hr : 0 ≤ r := by
    have := ht.1.trans ht.2
    linarith
  have hcmem : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  set φ : ℝ → ℝ := fun s => M / 2 * (s - c) ^ 2 - p.eval s with hφ
  set φ' : ℝ → ℝ := fun s => M * (s - c) - p.derivative.eval s with hφ'
  set φ'' : ℝ → ℝ := fun s => M - p.derivative.derivative.eval s with hφ''
  have hd : ∀ s : ℝ, HasDerivAt φ (φ' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => M / 2 * (s - c) ^ 2) (M / 2 * (2 * (s - c))) s := by
      have := ((hasDerivAt_id s).sub_const c).pow 2
      simpa using this.const_mul (M / 2)
    have h2 := p.hasDerivAt s
    have := h1.sub h2
    refine this.congr_deriv ?_
    rw [hφ']
    ring
  have hd' : ∀ s : ℝ, HasDerivAt φ' (φ'' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => M * (s - c)) M s := by
      simpa using ((hasDerivAt_id s).sub_const c).const_mul M
    have h2 := p.derivative.hasDerivAt s
    exact (h1.sub h2)
  have hderivφ : ∀ s, deriv φ s = φ' s := fun s => (hd s).deriv
  have hderivφ' : ∀ s, deriv φ' s = φ'' s := fun s => (hd' s).deriv
  have hφ'c : φ' c = 0 := by rw [hφ']; simp [hp']
  have hmono' : MonotoneOn φ' (Icc (c - r) (c + r)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun s _ => (hd' s).continuousAt.continuousWithinAt)
      (fun s _ => (hd' s).differentiableAt.differentiableWithinAt) (fun s hs => ?_)
    rw [interior_Icc] at hs
    rw [hderivφ', hφ'']
    have := hM s ⟨hs.1.le, hs.2.le⟩
    linarith
  rcases le_or_gt c t with hct | hct
  · have hsub : Icc c t ⊆ Icc (c - r) (c + r) := Icc_subset_Icc (by linarith) ht.2
    have hmonoφ : MonotoneOn φ (Icc c t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun s _ => (hd s).continuousAt.continuousWithinAt)
        (fun s _ => (hd s).differentiableAt.differentiableWithinAt) (fun s hs => ?_)
      rw [interior_Icc] at hs
      rw [hderivφ]
      have := hmono' hcmem (hsub ⟨hs.1.le, hs.2.le⟩) hs.1.le
      rw [hφ'c] at this
      exact this
    have := hmonoφ ⟨le_rfl, hct⟩ ⟨hct, le_rfl⟩ hct
    rw [hφ] at this
    simp only at this
    nlinarith [this]
  · have hsub : Icc t c ⊆ Icc (c - r) (c + r) := Icc_subset_Icc ht.1 (by linarith)
    have hantiφ : AntitoneOn φ (Icc t c) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun s _ => (hd s).continuousAt.continuousWithinAt)
        (fun s _ => (hd s).differentiableAt.differentiableWithinAt) (fun s hs => ?_)
      rw [interior_Icc] at hs
      rw [hderivφ]
      have := hmono' (hsub ⟨hs.1.le, hs.2.le⟩) hcmem hs.2.le
      rw [hφ'c] at this
      exact this
    have := hantiφ ⟨le_rfl, hct.le⟩ ⟨hct.le, le_rfl⟩ hct.le
    rw [hφ] at this
    simp only at this
    nlinarith [this]

/-- **The second-order Taylor bound at a critical point.**  If `|p''| ≤ M` on a window around a
critical point `c`, then `|p(t) - p(c)| ≤ M (t-c)²/2` on that window. -/
theorem abs_eval_sub_le_of_abs_second_derivative_bound {p : ℝ[X]} {c M r : ℝ}
    (hp' : p.derivative.eval c = 0)
    (hM : ∀ s ∈ Icc (c - r) (c + r), |p.derivative.derivative.eval s| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (c - r) (c + r)) :
    |p.eval t - p.eval c| ≤ M * (t - c) ^ 2 / 2 := by
  have h1 : p.eval t - p.eval c ≤ M * (t - c) ^ 2 / 2 :=
    eval_sub_le_aux hp' (fun s hs => le_trans (le_abs_self _) (hM s hs)) ht
  have h2 : (-p).eval t - (-p).eval c ≤ M * (t - c) ^ 2 / 2 := by
    refine eval_sub_le_aux (p := -p) (by simp [hp']) (fun s hs => ?_) ht
    simp only [derivative_neg, eval_neg]
    have := hM s hs
    have := neg_abs_le (p.derivative.derivative.eval s)
    linarith
  simp only [eval_neg] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ### Sign at the two ends -/

theorem eventually_pos_atTop_of_leadingCoeff_pos {P : ℝ[X]} (hdeg : 0 < P.natDegree)
    (hlead : 0 < P.leadingCoeff) : ∀ᶠ y in atTop, 0 < P.eval y := by
  have hd : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  exact (P.tendsto_atTop_of_leadingCoeff_nonneg hd hlead.le).eventually_gt_atTop 0

theorem eventually_pos_atBot_of_leadingCoeff_pos_of_even {P : ℝ[X]} (hdeg : 0 < P.natDegree)
    (hlead : 0 < P.leadingCoeff) (heven : Even P.natDegree) : ∀ᶠ y in atBot, 0 < P.eval y := by
  have hXne : ((-X : ℝ[X]).natDegree) ≠ 0 := by simp
  have hQdeg : (P.comp (-X : ℝ[X])).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp]
    simp
  have hQlead : (P.comp (-X : ℝ[X])).leadingCoeff = P.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp hXne]
    have h1 : ((-X : ℝ[X]).leadingCoeff) = -1 := by simp
    rw [h1, heven.neg_one_pow, mul_one]
  have hQeval : ∀ y : ℝ, (P.comp (-X : ℝ[X])).eval y = P.eval (-y) := by
    intro y
    simp [Polynomial.eval_comp]
  have h := eventually_pos_atTop_of_leadingCoeff_pos (P := P.comp (-X : ℝ[X]))
    (by rw [hQdeg]; exact hdeg) (by rw [hQlead]; exact hlead)
  rw [Filter.eventually_atTop] at h
  obtain ⟨a, ha⟩ := h
  rw [Filter.eventually_atBot]
  refine ⟨-a, fun z hz => ?_⟩
  have hz' := ha (-z) (by linarith)
  rwa [hQeval, neg_neg] at hz'

/-! ### (D3) The curvature window -/

/-- **The curvature window exists.**  Around a point where the second derivative does not vanish
there is a closed window, of any prescribed maximal radius, on which `|p''|` is bounded below by a
positive constant and keeps the sign it has at the centre. -/
theorem exists_curvature_window (p : ℝ[X]) {c : ℝ}
    (hc : p.derivative.derivative.eval c ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w, 0 < w ∧ w ≤ ρ ∧
      (∀ s ∈ Icc (c - w) (c + w),
        |p.derivative.derivative.eval c| / 2 ≤ |p.derivative.derivative.eval s|) ∧
      (∀ s ∈ Icc (c - w) (c + w),
        0 ≤ p.derivative.derivative.eval c * p.derivative.derivative.eval s) := by
  set q := p.derivative.derivative with hq
  have hcont : ContinuousAt (fun s => q.eval s) c := (q.continuous_aeval).continuousAt
  have hpos : 0 < |q.eval c| := abs_pos.mpr hc
  have hev : ∀ᶠ s in nhds c, |q.eval c| / 2 < |q.eval s| ∧ 0 < q.eval c * q.eval s := by
    have h1 : ∀ᶠ s in nhds c, |q.eval c| / 2 < |q.eval s| := by
      refine ContinuousAt.eventually_lt continuousAt_const hcont.abs ?_
      simpa using half_lt_self hpos
    have h2 : ∀ᶠ s in nhds c, 0 < q.eval c * q.eval s := by
      refine ContinuousAt.eventually_lt continuousAt_const (continuousAt_const.mul hcont) ?_
      simpa using mul_self_pos.mpr hc
    exact h1.and h2
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨min ρ (δ / 2), lt_min hρ (by linarith), min_le_left _ _, ?_, ?_⟩
  · intro s hs
    have hdist : dist s c < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have := hs.1
        have hm : min ρ (δ / 2) ≤ δ / 2 := min_le_right _ _
        linarith
      · have := hs.2
        have hm : min ρ (δ / 2) ≤ δ / 2 := min_le_right _ _
        linarith
    exact (hball hdist).1.le
  · intro s hs
    have hdist : dist s c < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have := hs.1
        have hm : min ρ (δ / 2) ≤ δ / 2 := min_le_right _ _
        linarith
      · have := hs.2
        have hm : min ρ (δ / 2) ≤ δ / 2 := min_le_right _ _
        linarith
    exact (hball hdist).2.le

/-! ### (W1) The shifted critical point -/

/-- **The perturbed critical point.**  On a window where `|C''| ≥ m > 0` with the sign it has at the
centre, a perturbation whose slope is bounded by `e < m·w` on that window moves the critical point
by at most `ε = e/m`.  The degenerate case `e = 0` is covered: the critical point does not move. -/
theorem exists_perturbed_critical_point {C D : ℝ[X]} {c m w e : ℝ}
    (hm : 0 < m) (he : 0 ≤ e) (hb : e < m * w)
    (hcrit : C.derivative.eval c = 0)
    (hcurv : ∀ s ∈ Icc (c - w) (c + w), m ≤ |C.derivative.derivative.eval s|)
    (hsgn : ∀ s ∈ Icc (c - w) (c + w),
      0 ≤ C.derivative.derivative.eval c * C.derivative.derivative.eval s)
    (hslope : ∀ s ∈ Icc (c - w) (c + w), |D.derivative.eval s| ≤ e) :
    ∃ c', |c' - c| ≤ e / m ∧ (C + D).derivative.eval c' = 0 := by
  set ε : ℝ := e / m with hεdef
  have hε0 : 0 ≤ ε := div_nonneg he hm.le
  have hmε : m * ε = e := by
    rw [hεdef, mul_div_cancel₀ _ hm.ne']
  have hw : 0 < w := by nlinarith
  have hεw : ε < w := by
    rw [hεdef, div_lt_iff₀ hm]
    linarith
  have hmem : ∀ t : ℝ, |t - c| ≤ ε → t ∈ Icc (c - w) (c + w) := by
    intro t ht
    rw [abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcmem : c ∈ Icc (c - w) (c + w) := hmem c (by simpa using hε0)
  set σ : ℝ := C.derivative.derivative.eval c with hσdef
  have hσ : σ ≠ 0 := by
    intro h
    have h1 := hcurv c hcmem
    rw [← hσdef, h] at h1
    simp at h1
    linarith
  set sgn : ℝ := if 0 < σ then (1 : ℝ) else -1 with hsgndef
  have hsgnsq : sgn * sgn = 1 := by
    rw [hsgndef]; split_ifs <;> norm_num
  have hsgnne : sgn ≠ 0 := by
    rw [hsgndef]; split_ifs <;> norm_num
  have hkey : ∀ s ∈ Icc (c - w) (c + w), m ≤ sgn * C.derivative.derivative.eval s := by
    intro s hs
    have h1 := hsgn s hs
    have h2 := hcurv s hs
    rcases lt_or_gt_of_ne hσ with hneg | hpos
    · have hsg : sgn = -1 := by rw [hsgndef]; exact if_neg (by linarith)
      have hle : C.derivative.derivative.eval s ≤ 0 := by nlinarith
      rw [hsg]
      rw [abs_of_nonpos hle] at h2
      linarith
    · have hsg : sgn = 1 := by rw [hsgndef]; exact if_pos hpos
      have hge : 0 ≤ C.derivative.derivative.eval s := by nlinarith
      rw [hsg]
      rw [abs_of_nonneg hge] at h2
      linarith
  -- the two endpoint estimates for `C'`
  have hplus : m * ε ≤ sgn * C.derivative.eval (c + ε) := by
    rcases eq_or_lt_of_le hε0 with hz | hz
    · rw [← hz]
      simp [hcrit]
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
        (fun t => C.derivative.eval t) (fun t => C.derivative.derivative.eval t)
        (show c < c + ε by linarith)
        (C.derivative.continuous_aeval).continuousOn
        (fun t _ => C.derivative.hasDerivAt t)
      have hmemξ : ξ ∈ Icc (c - w) (c + w) :=
        ⟨by linarith [hξ.1], by linarith [hξ.2, hεw]⟩
      have hεne : ε ≠ 0 := ne_of_gt hz
      have hval : C.derivative.eval (c + ε) = C.derivative.derivative.eval ξ * ε := by
        simp only [hcrit, sub_zero, add_sub_cancel_left] at hξeq
        rw [eq_div_iff hεne] at hξeq
        linarith [hξeq]
      rw [hval, ← mul_assoc]
      have := hkey ξ hmemξ
      nlinarith
  have hminus : sgn * C.derivative.eval (c - ε) ≤ -(m * ε) := by
    rcases eq_or_lt_of_le hε0 with hz | hz
    · rw [← hz]
      simp [hcrit]
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
        (fun t => C.derivative.eval t) (fun t => C.derivative.derivative.eval t)
        (show c - ε < c by linarith)
        (C.derivative.continuous_aeval).continuousOn
        (fun t _ => C.derivative.hasDerivAt t)
      have hmemξ : ξ ∈ Icc (c - w) (c + w) :=
        ⟨by linarith [hξ.1, hεw], by linarith [hξ.2]⟩
      have hεne : ε ≠ 0 := ne_of_gt hz
      have hval : C.derivative.eval (c - ε) = -(C.derivative.derivative.eval ξ * ε) := by
        simp only [hcrit, zero_sub, sub_sub_cancel] at hξeq
        rw [eq_div_iff hεne] at hξeq
        linarith [hξeq]
      rw [hval]
      have := hkey ξ hmemξ
      nlinarith
  -- transfer to the perturbed derivative
  set g : ℝ → ℝ := fun t => sgn * (C + D).derivative.eval t with hgdef
  have hgcont : ContinuousOn g (Icc (c - ε) (c + ε)) :=
    (continuous_const.mul (C + D).derivative.continuous_aeval).continuousOn
  have hgminus : g (c - ε) ≤ 0 := by
    have hd := hslope (c - ε) (hmem _ (by rw [abs_le]; constructor <;> linarith))
    rw [abs_le] at hd
    have hsd : sgn * D.derivative.eval (c - ε) ≤ e := by
      rw [hsgndef]; split_ifs <;> [linarith [hd.2]; linarith [hd.1]]
    rw [hgdef]
    simp only [Polynomial.derivative_add, Polynomial.eval_add, mul_add]
    linarith [hminus, hsd, hmε]
  have hgplus : 0 ≤ g (c + ε) := by
    have hd := hslope (c + ε) (hmem _ (by rw [abs_le]; constructor <;> linarith))
    rw [abs_le] at hd
    have hsd : -e ≤ sgn * D.derivative.eval (c + ε) := by
      rw [hsgndef]; split_ifs <;> [linarith [hd.1]; linarith [hd.2]]
    rw [hgdef]
    simp only [Polynomial.derivative_add, Polynomial.eval_add, mul_add]
    linarith [hplus, hsd, hmε]
  have hsub : Icc (g (c - ε)) (g (c + ε)) ⊆ g '' Icc (c - ε) (c + ε) :=
    intermediate_value_Icc (by linarith) hgcont
  obtain ⟨c', hc'mem, hc'val⟩ := hsub ⟨hgminus, hgplus⟩
  refine ⟨c', ?_, ?_⟩
  · rw [abs_le]
    exact ⟨by linarith [hc'mem.1], by linarith [hc'mem.2]⟩
  · have : sgn * (C + D).derivative.eval c' = 0 := hc'val
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hsgnne
    · exact h

/-! ### The localized `C¹` perturbation lemma -/

private theorem mul_pos_of_abs_sub_lt {a b : ℝ} (h : |a - b| < |b|) : 0 < a * b := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [abs_of_neg hb, abs_lt] at h
    nlinarith [h.1, h.2]
  · exfalso
    rw [hb, sub_zero, abs_zero] at h
    linarith [abs_nonneg a]
  · rw [abs_of_pos hb, abs_lt] at h
    nlinarith [h.1, h.2]

/-- **The localized `C¹` perturbation lemma.**  A hyperbolic polynomial `C` with simple critical
points and nonvanishing critical values stays hyperbolic under a deformation `D` whose slope and
value are small on curvature windows around the critical points.

The hypotheses are exactly the card's `(b_i′)` (`hbcond`: the window slope bound `e i` is below
`m i · w i`) and `(a_i″)` (`hacond`: the value bound plus the second-order term stays below the
critical value), with `m i` the window-minimum curvature, `M i` the window-maximum curvature and
`ε i = e i / m i` the displacement radius.  The degenerate case `e i = 0` is covered. -/
theorem hyperbolic_of_localized_perturbation
    {C D : ℝ[X]} {n : ℕ} {x w m e ε M dbnd : ℕ → ℝ}
    (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C) (hn : 0 < n)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    (hDdeg : D.natDegree ≤ n + 1)
    (hlead : |D.coeff (n + 1)| < |C.coeff (n + 1)|)
    (hm : ∀ i, i < n → 0 < m i)
    (hwgap : ∀ i, i + 1 < n → x i + w i ≤ x (i + 1) - w (i + 1))
    (hcurv : ∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i),
      m i ≤ |C.derivative.derivative.eval s|)
    (hsgnw : ∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i),
      0 ≤ C.derivative.derivative.eval (x i) * C.derivative.derivative.eval s)
    (hMbound : ∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i),
      |C.derivative.derivative.eval s| ≤ M i)
    (he0 : ∀ i, i < n → 0 ≤ e i)
    (hslope : ∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i), |D.derivative.eval s| ≤ e i)
    (hbcond : ∀ i, i < n → e i < m i * w i)
    (hεdef : ∀ i, i < n → ε i = e i / m i)
    (hdb : ∀ i, i < n → ∀ t ∈ Icc (x i - ε i) (x i + ε i), |D.eval t| ≤ dbnd i)
    (hacond : ∀ i, i < n → dbnd i + M i * (ε i) ^ 2 / 2 < |C.eval (x i)|) :
    Hyperbolic (C + D) := by
  classical
  set F : ℝ[X] := C + D with hF
  -- basic window facts
  have hw0 : ∀ i, i < n → 0 < w i := by
    intro i hi
    nlinarith [he0 i hi, hbcond i hi, hm i hi]
  have hε0 : ∀ i, i < n → 0 ≤ ε i := by
    intro i hi
    rw [hεdef i hi]
    exact div_nonneg (he0 i hi) (hm i hi).le
  have hεw : ∀ i, i < n → ε i < w i := by
    intro i hi
    rw [hεdef i hi, div_lt_iff₀ (hm i hi)]
    linarith [hbcond i hi]
  -- (W1) the perturbed critical points
  have hex : ∀ i, i < n → ∃ c', |c' - x i| ≤ ε i ∧ F.derivative.eval c' = 0 := by
    intro i hi
    have h := exists_perturbed_critical_point (C := C) (D := D) (c := x i) (m := m i)
      (w := w i) (e := e i) (hm i hi) (he0 i hi) (hbcond i hi) (hcrit i hi) (hcurv i hi)
      (hsgnw i hi) (hslope i hi)
    rw [← hεdef i hi] at h
    exact h
  choose! x' hx'1 hx'2 using hex
  -- (ii) the sign of the critical value is preserved
  have hsignpres : ∀ i, i < n → 0 < F.eval (x' i) * C.eval (x i) := by
    intro i hi
    refine mul_pos_of_abs_sub_lt ?_
    have hmemw : x' i ∈ Icc (x i - w i) (x i + w i) := by
      have h := abs_le.mp (hx'1 i hi)
      have hwe := hεw i hi
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hmemε : x' i ∈ Icc (x i - ε i) (x i + ε i) := by
      have h := abs_le.mp (hx'1 i hi)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have htaylor : |C.eval (x' i) - C.eval (x i)| ≤ M i * (x' i - x i) ^ 2 / 2 :=
      abs_eval_sub_le_of_abs_second_derivative_bound (hcrit i hi) (hMbound i hi) hmemw
    have hsq : (x' i - x i) ^ 2 ≤ (ε i) ^ 2 := by
      have h := hx'1 i hi
      have h0 := abs_nonneg (x' i - x i)
      calc (x' i - x i) ^ 2 = |x' i - x i| ^ 2 := (sq_abs _).symm
        _ ≤ (ε i) ^ 2 := by nlinarith [hε0 i hi]
    have hMnn : 0 ≤ M i := le_trans (abs_nonneg _) (hMbound i hi (x i) ⟨by linarith [hw0 i hi],
      by linarith [hw0 i hi]⟩)
    have hD : |D.eval (x' i)| ≤ dbnd i := hdb i hi (x' i) hmemε
    have hsum : |F.eval (x' i) - C.eval (x i)| ≤ dbnd i + M i * (ε i) ^ 2 / 2 := by
      have hsplit : F.eval (x' i) - C.eval (x i)
          = D.eval (x' i) + (C.eval (x' i) - C.eval (x i)) := by
        rw [hF]; simp; ring
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      have : M i * (x' i - x i) ^ 2 / 2 ≤ M i * (ε i) ^ 2 / 2 := by nlinarith
      linarith
    exact lt_of_le_of_lt hsum (hacond i hi)
  -- the perturbed critical points are increasing
  have hx'mono : ∀ i, i + 1 < n → x' i < x' (i + 1) := by
    intro i hi
    have h1 := abs_le.mp (hx'1 i (by omega))
    have h2 := abs_le.mp (hx'1 (i + 1) (by omega))
    have h3 := hεw i (by omega)
    have h4 := hεw (i + 1) (by omega)
    have h5 := hwgap i hi
    linarith [h1.2, h2.1]
  -- (iii) the alternation at the perturbed critical points
  have halt : ∀ i, i + 1 < n → F.eval (x' i) * F.eval (x' (i + 1)) < 0 := by
    intro i hi
    have hC := eval_mul_eval_succ_neg hdeg hhyp hxmono hcrit hxne hi
    have h1 := hsignpres i (by omega)
    have h2 := hsignpres (i + 1) (by omega)
    nlinarith [mul_pos h1 h2]
  -- the preserved leading sign gives the two outer sign changes
  have hC0 : C ≠ 0 := ne_zero_of_natDegree_eq_succ hdeg
  have hFdeg : F.natDegree ≤ n + 1 := by
    rw [hF]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp [hdeg, hDdeg]
  have hCcoeff : C.coeff (n + 1) ≠ 0 := by
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hC0
  have hFcoeff : F.coeff (n + 1) = C.coeff (n + 1) + D.coeff (n + 1) := by
    rw [hF]; simp
  have hFCpos : 0 < F.coeff (n + 1) * C.coeff (n + 1) := by
    rw [hFcoeff]
    have h2 : -(|C.coeff (n + 1)|) < D.coeff (n + 1) := by
      have := neg_abs_le (D.coeff (n + 1)); linarith
    have h3 : D.coeff (n + 1) < |C.coeff (n + 1)| := by
      have := le_abs_self (D.coeff (n + 1)); linarith
    rcases abs_cases (C.coeff (n + 1)) with ⟨hc, hcp⟩ | ⟨hc, hcn⟩
    · nlinarith
    · nlinarith
  have hFcoeffne : F.coeff (n + 1) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hFCpos
    exact lt_irrefl 0 hFCpos
  have hF0 : F ≠ 0 := fun h => hFcoeffne (by rw [h]; simp)
  have hFnatDeg : F.natDegree = n + 1 :=
    le_antisymm hFdeg (Polynomial.le_natDegree_of_ne_zero hFcoeffne)
  have hPdeg : (F * C).natDegree = 2 * (n + 1) := by
    rw [Polynomial.natDegree_mul hF0 hC0, hFnatDeg, hdeg]
    ring
  have hPlead : 0 < (F * C).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul]
    have h1 : F.leadingCoeff = F.coeff (n + 1) := by rw [Polynomial.leadingCoeff, hFnatDeg]
    have h2 : C.leadingCoeff = C.coeff (n + 1) := by rw [Polynomial.leadingCoeff, hdeg]
    rw [h1, h2]
    exact hFCpos
  have hPeven : Even (F * C).natDegree := by rw [hPdeg]; exact even_two_mul _
  have hPtop := eventually_pos_atTop_of_leadingCoeff_pos (P := F * C) (by rw [hPdeg]; omega) hPlead
  have hPbot := eventually_pos_atBot_of_leadingCoeff_pos_of_even (P := F * C)
    (by rw [hPdeg]; omega) hPlead hPeven
  rw [Filter.eventually_atTop] at hPtop
  rw [Filter.eventually_atBot] at hPbot
  obtain ⟨a₁, ha₁⟩ := hPtop
  obtain ⟨a₀, ha₀⟩ := hPbot
  obtain ⟨r₀, hr₀lt, hr₀0⟩ := exists_root_lt_first hdeg hhyp hxmono hcrit hxne hn
  obtain ⟨r₁, hr₁gt, hr₁0⟩ := exists_root_gt_last hdeg hhyp hxmono hcrit hxne hn
  set y₀ : ℝ := min a₀ (min (r₀ - 1) (x 0 - w 0 - 1)) with hy₀def
  set y₁ : ℝ := max a₁ (max (r₁ + 1) (x (n - 1) + w (n - 1) + 1)) with hy₁def
  have hy₀a : y₀ ≤ a₀ := min_le_left _ _
  have hy₀r : y₀ < r₀ := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hy₀x : y₀ < x 0 - w 0 :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  have hy₁a : a₁ ≤ y₁ := le_max_left _ _
  have hy₁r : r₁ < y₁ := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hy₁x : x (n - 1) + w (n - 1) < y₁ :=
    lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hPy₀ : 0 < (F * C).eval y₀ := ha₀ y₀ hy₀a
  have hPy₁ : 0 < (F * C).eval y₁ := ha₁ y₁ hy₁a
  have hFCy₀ : 0 < F.eval y₀ * C.eval y₀ := by simpa using hPy₀
  have hFCy₁ : 0 < F.eval y₁ * C.eval y₁ := by simpa using hPy₁
  -- the unperturbed sign changes at the two ends
  have hCy₀ : C.eval y₀ * C.eval (x 0) < 0 := by
    refine eval_mul_eval_neg_of_root_mem_Ioo ?_ ⟨hy₀r, hr₀lt⟩ hr₀0
    refine strictMonoOn_or_strictAntiOn_of_derivative_ne_zero ?_
    intro z hz
    refine derivative_ne_zero_of_notMem hdeg hxmono hcrit ?_
    intro j hj hzx
    subst hzx
    have := index_lt_of_eval_lt hxmono hj hz.2
    omega
  have hCy₁ : C.eval (x (n - 1)) * C.eval y₁ < 0 := by
    refine eval_mul_eval_neg_of_root_mem_Ioo ?_ ⟨hr₁gt, hy₁r⟩ hr₁0
    refine strictMonoOn_or_strictAntiOn_of_derivative_ne_zero ?_
    intro z hz
    refine derivative_ne_zero_of_notMem hdeg hxmono hcrit ?_
    intro j hj hzx
    subst hzx
    have := index_lt_of_eval_lt hxmono (show n - 1 < n by omega) hz.1
    omega
  -- transfer to `F`
  have hFy₀ : F.eval y₀ * F.eval (x' 0) < 0 := by
    have h1 := hsignpres 0 hn
    nlinarith [mul_pos hFCy₀ h1]
  have hFy₁ : F.eval (x' (n - 1)) * F.eval y₁ < 0 := by
    have h1 := hsignpres (n - 1) (by omega)
    nlinarith [mul_pos h1 hFCy₁]
  -- the endpoints sit outside the perturbed critical points
  have hy₀x' : y₀ < x' 0 := by
    have h := abs_le.mp (hx'1 0 hn)
    have := hεw 0 hn
    linarith [h.1]
  have hy₁x' : x' (n - 1) < y₁ := by
    have h := abs_le.mp (hx'1 (n - 1) (by omega))
    have := hεw (n - 1) (by omega)
    linarith [h.2]
  -- assemble the `n + 2` alternating points
  refine hyperbolic_of_sign_changes (d := n + 1)
    (y := fun k => if k = 0 then y₀ else if k ≤ n then x' (k - 1) else y₁) hFdeg ?_ ?_
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [if_pos rfl, if_neg (by omega : (0 : ℕ) + 1 ≠ 0), if_pos (by omega : 0 + 1 ≤ n)]
      simpa using hy₀x'
    · rw [if_neg (by omega : k ≠ 0), if_pos (show k ≤ n by omega)]
      rcases Nat.lt_or_ge k n with hlt | hge
      · rw [if_neg (by omega : k + 1 ≠ 0), if_pos (show k + 1 ≤ n by omega)]
        have h := hx'mono (k - 1) (by omega)
        have hk1 : k - 1 + 1 = k := by omega
        rw [hk1] at h
        have hk2 : k + 1 - 1 = k := by omega
        rw [hk2]
        exact h
      · have hkn' : k = n := by omega
        rw [if_neg (by omega : k + 1 ≠ 0), if_neg (show ¬ (k + 1 ≤ n) by omega), hkn']
        exact hy₁x'
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [if_pos rfl, if_neg (by omega : (0 : ℕ) + 1 ≠ 0), if_pos (by omega : 0 + 1 ≤ n)]
      simpa using hFy₀
    · rw [if_neg (by omega : k ≠ 0), if_pos (show k ≤ n by omega)]
      rcases Nat.lt_or_ge k n with hlt | hge
      · rw [if_neg (by omega : k + 1 ≠ 0), if_pos (show k + 1 ≤ n by omega)]
        have h := halt (k - 1) (by omega)
        have hk1 : k - 1 + 1 = k := by omega
        rw [hk1] at h
        have hk2 : k + 1 - 1 = k := by omega
        rw [hk2]
        exact h
      · have hkn' : k = n := by omega
        rw [if_neg (by omega : k + 1 ≠ 0), if_neg (show ¬ (k + 1 ≤ n) by omega), hkn']
        exact hFy₁

/-! ### (D1)–(D3) The window data always exists -/

/-- **The perturbation windows exist.**  For any strictly increasing family of points at which the
second derivative does not vanish there are pairwise disjoint closed windows carrying a positive
curvature lower bound, constant curvature sign, and a finite curvature upper bound.  So the
hypotheses of `hyperbolic_of_localized_perturbation` are never vacuous: the window data of the
card's `(D1)`–`(D3)` is total. -/
theorem exists_perturbation_windows {C : ℝ[X]} {n : ℕ} {x : ℕ → ℝ}
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hsimple : ∀ i, i < n → C.derivative.derivative.eval (x i) ≠ 0) :
    ∃ w m M : ℕ → ℝ,
      (∀ i, i < n → 0 < w i) ∧
      (∀ i, i < n → 0 < m i) ∧
      (∀ i, i + 1 < n → x i + w i ≤ x (i + 1) - w (i + 1)) ∧
      (∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i),
        m i ≤ |C.derivative.derivative.eval s|) ∧
      (∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i),
        0 ≤ C.derivative.derivative.eval (x i) * C.derivative.derivative.eval s) ∧
      (∀ i, i < n → ∀ s ∈ Icc (x i - w i) (x i + w i),
        |C.derivative.derivative.eval s| ≤ M i) := by
  classical
  -- a uniform radius small enough for disjointness
  obtain ⟨ρ, hρ0, hρgap⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, i + 1 < n → 3 * ρ ≤ x (i + 1) - x i := by
    by_cases hn1 : n ≤ 1
    · exact ⟨1, one_pos, fun i hi => absurd hi (by omega)⟩
    · have hne : (Finset.range (n - 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
      refine ⟨(Finset.range (n - 1)).inf' hne (fun i => (x (i + 1) - x i) / 3), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        have := hxmono i (i + 1) (by omega) (by omega)
        linarith
      · intro i hi
        have hmem : i ∈ Finset.range (n - 1) := Finset.mem_range.mpr (by omega)
        have := Finset.inf'_le (s := Finset.range (n - 1)) (fun i => (x (i + 1) - x i) / 3) hmem
        linarith
  -- a curvature window at each critical point
  have hex : ∀ i, ∃ wi : ℝ, 0 < wi ∧ wi ≤ ρ ∧
      (i < n → (∀ s ∈ Icc (x i - wi) (x i + wi),
        |C.derivative.derivative.eval (x i)| / 2 ≤ |C.derivative.derivative.eval s|) ∧
       (∀ s ∈ Icc (x i - wi) (x i + wi),
        0 ≤ C.derivative.derivative.eval (x i) * C.derivative.derivative.eval s)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨wi, hwi0, hwiρ, h1, h2⟩ := exists_curvature_window C (hsimple i hi) hρ0
      exact ⟨wi, hwi0, hwiρ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨ρ, hρ0, le_rfl, fun h => absurd h hi⟩
  choose w hw0 hwρ hwprop using hex
  -- a curvature upper bound on each window
  have hexM : ∀ i, ∃ Mi : ℝ, ∀ s ∈ Icc (x i - w i) (x i + w i),
      |C.derivative.derivative.eval s| ≤ Mi := by
    intro i
    obtain ⟨Mi, hMi⟩ := (isCompact_Icc (a := x i - w i) (b := x i + w i)).exists_bound_of_continuousOn
      (C.derivative.derivative.continuous_aeval).continuousOn
    exact ⟨Mi, fun s hs => by simpa using hMi s hs⟩
  choose M hM using hexM
  refine ⟨w, fun i => |C.derivative.derivative.eval (x i)| / 2, M,
    fun i _ => hw0 i, fun i hi => ?_, fun i hi => ?_, fun i hi => (hwprop i hi).1,
    fun i hi => (hwprop i hi).2, fun i _ => hM i⟩
  · exact half_pos (abs_pos.mpr (hsimple i hi))
  · have h1 := hwρ i
    have h2 := hwρ (i + 1)
    have h3 := hρgap i hi
    linarith

end GaloisForLFunctions.SignAlternation
