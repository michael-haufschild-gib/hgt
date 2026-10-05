import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus

/-!
# Flat growth under Volterra convolution

For `(f ⋆ g)(t) = ∫₀^t f(t - s) g(s) ds`:

* order: nonnegativity, strict positivity and monotone comparison on `[0, t]`, and the monomial
  law `(s^j/j!) ⋆ (s^k/k!) = t^{j+k+1}/(j+k+1)!`;
* logarithmic slope control: `f' ≤ εf` on `[T₀, ∞)` gives `f(t) ≤ f(s) e^{ε(t-s)}`; a vanishing
  logarithmic slope gives uniform fixed-shift flatness `f(t - v)/f(t) → 1` on every `[0, R]` and
  subexponential growth;
* propagation: if `g ≥ 0` is flat and `k ≥ 0` has divergent mass, then `(g ⋆ k)/g → ∞` and
  `(∫₀^t g)/g(t) → ∞`; if moreover `g` is nondecreasing, `k(0) = 0`, `k' ≥ 0` and `k'/k → 0`, then
  `(g ⋆ k)' = k' ⋆ g` and `(g ⋆ k)'/(g ⋆ k) → 0`.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Order and monomials -/

theorem volterraConv_nonneg_of_nonneg {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, 0 ≤ f s) (hg : ∀ s ∈ Icc 0 t, 0 ≤ g s) : 0 ≤ volterraConv f g t :=
  intervalIntegral.integral_nonneg ht fun s hs =>
    mul_nonneg (hf _ ⟨by linarith [hs.2], by linarith [hs.1]⟩) (hg s hs)

theorem volterraConv_pos_of_pos {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ s, 0 < s → 0 < f s) (hgp : ∀ s, 0 < s → 0 < g s) {t : ℝ} (ht : 0 < t) :
    0 < volterraConv f g t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun s => f (t - s) * g s).intervalIntegrable _ _)
    (fun s hs => mul_pos (hfp _ (by linarith [hs.2])) (hgp _ hs.1)) ht

theorem volterraConv_le_of_nonneg {f₁ f₂ g₁ g₂ : ℝ → ℝ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, 0 ≤ f₁ s ∧ f₁ s ≤ f₂ s) (hg : ∀ s ∈ Icc 0 t, 0 ≤ g₁ s ∧ g₁ s ≤ g₂ s) :
    volterraConv f₁ g₁ t ≤ volterraConv f₂ g₂ t :=
  intervalIntegral.integral_mono_on ht
    ((by fun_prop : Continuous fun s => f₁ (t - s) * g₁ s).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s => f₂ (t - s) * g₂ s).intervalIntegrable _ _) fun s hs => by
      have h1 := hf (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 := hg s hs
      exact mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)

/-- **Monomial law.**  `(s^j/j!) ⋆ (s^k/k!) = t^{j+k+1}/(j+k+1)!`. -/
theorem volterraConv_pow_div_factorial (j k : ℕ) (t : ℝ) :
    volterraConv (fun s => s ^ j / (j.factorial : ℝ)) (fun s => s ^ k / (k.factorial : ℝ)) t =
      t ^ (j + k + 1) / ((j + k + 1).factorial : ℝ) := by
  induction j generalizing t with
  | zero =>
    have e : (fun s : ℝ => s ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ)) = fun _ => 1 := by
      funext s; simp
    rw [e, volterraConv_one_left, intervalIntegral.integral_div, integral_pow, zero_add,
      Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero k), sub_zero]
    field_simp
  | succ j ih =>
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ (j + 1) / ((j + 1).factorial : ℝ))
        (s ^ j / (j.factorial : ℝ)) s := fun s => by
      refine ((hasDerivAt_pow (j + 1) s).div_const ((j + 1).factorial : ℝ)).congr_deriv ?_
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [volterraConv_eq_integral_of_hasDerivAt hd (by fun_prop) (by fun_prop)]
    simp_rw [ih]
    have h0 : (0 : ℝ) ^ (j + 1) / ((j + 1).factorial : ℝ) = 0 := by simp
    rw [h0, zero_mul, zero_add, intervalIntegral.integral_div, integral_pow]
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      sub_zero]
    rw [show j + 1 + k + 1 = (j + k + 1) + 1 by ring, Nat.factorial_succ (j + k + 1)]
    push_cast
    field_simp

/-! ## Logarithmic slope control -/

/-- `f' ≤ ε f` on `[T₀, ∞)` gives `f(t) ≤ f(s) e^{ε (t - s)}` for `T₀ ≤ s ≤ t`. -/
theorem le_mul_exp_of_deriv_le {f f' : ℝ → ℝ} {T₀ ε : ℝ}
    (hf : ∀ t, T₀ ≤ t → HasDerivAt f (f' t) t) (hslope : ∀ t, T₀ ≤ t → f' t ≤ ε * f t)
    {s t : ℝ} (hs : T₀ ≤ s) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (ε * (t - s)) := by
  have hd : ∀ x, T₀ ≤ x → HasDerivAt (fun x => f x * Real.exp (-(ε * x)))
      (f' x * Real.exp (-(ε * x)) + f x * (Real.exp (-(ε * x)) * -ε)) x := fun x hx => by
    have he : HasDerivAt (fun x => Real.exp (-(ε * x))) (Real.exp (-(ε * x)) * -ε) x := by
      have := ((hasDerivAt_id x).const_mul ε).neg.exp
      simpa using this
    exact (hf x hx).mul he
  have hφ : AntitoneOn (fun x => f x * Real.exp (-(ε * x))) (Ici T₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici T₀)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ici]
      exact fun x hx => (hd x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(hd x (le_of_lt hx)).deriv]
      have h1 := hslope x (le_of_lt hx)
      have he := Real.exp_pos (-(ε * x))
      nlinarith
  have h := hφ (show s ∈ Ici T₀ from hs) (show t ∈ Ici T₀ from hs.trans hst) hst
  simp only at h
  have e : Real.exp (ε * (t - s)) = Real.exp (-(ε * s)) / Real.exp (-(ε * t)) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, ← mul_div_assoc, le_div_iff₀ (Real.exp_pos _)]
  exact h

private theorem slope_window {f f' : ℝ → ℝ} (hf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t)
    (hpos : ∀ᶠ t in atTop, 0 < f t) (hslope : Tendsto (fun t => f' t / f t) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀, ∀ t, T₀ ≤ t → HasDerivAt f (f' t) t ∧ 0 < f t ∧ f' t ≤ ε * f t := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1
    (hf.and (hpos.and (hslope.eventually (gt_mem_nhds hε))))
  refine ⟨T₀, fun t ht => ⟨(hT₀ t ht).1, (hT₀ t ht).2.1, ?_⟩⟩
  have h := (hT₀ t ht).2.2
  rw [div_lt_iff₀ (hT₀ t ht).2.1] at h
  exact h.le

/-- **Fixed-shift flatness.**  A vanishing logarithmic slope gives `c f(t) ≤ f(t - v)` for all
large `t`, uniformly for `v ∈ [0, R]`, for every `c < 1`. -/
theorem eventually_mul_le_shift_of_slope {f f' : ℝ → ℝ} (hf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t)
    (hpos : ∀ᶠ t in atTop, 0 < f t) (hslope : Tendsto (fun t => f' t / f t) atTop (𝓝 0))
    {R c : ℝ} (hR : 0 ≤ R) (hc : c < 1) :
    ∀ᶠ t in atTop, ∀ v ∈ Icc 0 R, c * f t ≤ f (t - v) := by
  set ε := (1 - c) / (R + 1) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨T₀, hT₀⟩ := slope_window hf hpos hslope hε
  filter_upwards [eventually_ge_atTop (T₀ + R)] with t ht v hv
  have hs : T₀ ≤ t - v := by linarith [hv.2]
  have key := le_mul_exp_of_deriv_le (fun x hx => (hT₀ x hx).1) (fun x hx => (hT₀ x hx).2.2) hs
    (by linarith [hv.1] : t - v ≤ t)
  rw [sub_sub_cancel] at key
  have hft := (hT₀ t (by linarith)).2.1
  have hfs := (hT₀ (t - v) hs).2.1
  have h1 : f t * Real.exp (-(ε * v)) ≤ f (t - v) := by
    have := mul_le_mul_of_nonneg_right key (Real.exp_pos (-(ε * v))).le
    rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
  have h2 : 1 - ε * v ≤ Real.exp (-(ε * v)) := by linarith [Real.add_one_le_exp (-(ε * v))]
  have h3 : ε * v ≤ 1 - c := by
    have : ε * v ≤ ε * R := mul_le_mul_of_nonneg_left hv.2 hε.le
    have : ε * R ≤ 1 - c := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  nlinarith

/-- Fixed-shift flatness with monotonicity: `f(t - v)/f(t) → 1` uniformly on `[0, R]`. -/
theorem tendstoUniformlyOn_shift_ratio_of_slope {f f' : ℝ → ℝ}
    (hf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t) (hpos : ∀ᶠ t in atTop, 0 < f t)
    (hslope : Tendsto (fun t => f' t / f t) atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hmono : ∀ᶠ t in atTop, ∀ v ∈ Icc 0 R, f (t - v) ≤ f t) :
    TendstoUniformlyOn (fun t v => f (t - v) / f t) (fun _ => 1) atTop (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_mul_le_shift_of_slope hf hpos hslope hR (by linarith : 1 - ε / 2 < 1),
    hmono, hpos] with t hlow hup hft v hv
  rw [Real.dist_eq, abs_lt]
  have h1 := hlow v hv
  have h2 := hup v hv
  constructor
  · rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hft]
    nlinarith
  · rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hft]
    nlinarith

/-- **Subexponential growth.**  A vanishing logarithmic slope gives `t e^{-βt} f(t) → 0`. -/
theorem tendsto_mul_exp_neg_mul_of_slope {f f' : ℝ → ℝ}
    (hf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t) (hpos : ∀ᶠ t in atTop, 0 < f t)
    (hslope : Tendsto (fun t => f' t / f t) atTop (𝓝 0)) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun t => t * Real.exp (-(β * t)) * f t) atTop (𝓝 0) := by
  obtain ⟨T₀, hT₀⟩ := slope_window hf hpos hslope (half_pos hβ)
  set C := f T₀ * Real.exp (-(β / 2 * T₀)) * (2 / β)
  have hlim : Tendsto (fun t => C * ((β / 2 * t) ^ 1 * Real.exp (-(β / 2 * t)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((tendsto_id.const_mul_atTop (half_pos hβ)))
    simpa using h.const_mul C
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (max T₀ 0)] with t ht
    have h0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    exact mul_nonneg (mul_nonneg h0 (Real.exp_pos _).le) (hT₀ t ((le_max_left _ _).trans ht)).2.1.le
  · filter_upwards [eventually_ge_atTop (max T₀ 0)] with t ht
    have hT := (le_max_left _ _).trans ht
    have h0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have key := le_mul_exp_of_deriv_le (fun x hx => (hT₀ x hx).1) (fun x hx => (hT₀ x hx).2.2)
      le_rfl hT
    have hpos' : 0 ≤ t * Real.exp (-(β * t)) := mul_nonneg h0 (Real.exp_pos _).le
    calc t * Real.exp (-(β * t)) * f t
        ≤ t * Real.exp (-(β * t)) * (f T₀ * Real.exp (β / 2 * (t - T₀))) :=
          mul_le_mul_of_nonneg_left key hpos'
      _ = t * f T₀ * (Real.exp (-(β * t)) * Real.exp (β / 2 * (t - T₀))) := by ring
      _ = C * ((β / 2 * t) ^ 1 * Real.exp (-(β / 2 * t))) := by
          have e : Real.exp (-(β * t)) * Real.exp (β / 2 * (t - T₀)) =
              Real.exp (-(β / 2 * T₀)) * Real.exp (-(β / 2 * t)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          rw [e]
          simp only [C, pow_one]
          field_simp

/-! ## Propagation through convolution -/

/-- **Mass escape.**  For a nonnegative flat `g` and a nonnegative `k` of divergent mass,
`(g ⋆ k)/g → ∞`. -/
theorem tendsto_volterraConv_div_atTop {g k : ℝ → ℝ} (hg : Continuous g) (hk : Continuous k)
    (hgnn : ∀ s, 0 ≤ s → 0 ≤ g s) (hknn : ∀ s, 0 ≤ s → 0 ≤ k s) (hpos : ∀ᶠ t in atTop, 0 < g t)
    (hshift : ∀ R c, 0 ≤ R → c < 1 → ∀ᶠ t in atTop, ∀ v ∈ Icc 0 R, c * g t ≤ g (t - v))
    (hmass : Tendsto (fun R => ∫ s in (0 : ℝ)..R, k s) atTop atTop) :
    Tendsto (fun t => volterraConv g k t / g t) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  obtain ⟨R, hRM, hR0⟩ :=
    ((hmass.eventually (eventually_ge_atTop (2 * M))).and (eventually_ge_atTop 0)).exists
  filter_upwards [hpos, hshift R (1 / 2) hR0 (by norm_num), eventually_ge_atTop R] with t hpt hsh htR
  rw [le_div_iff₀ hpt]
  unfold volterraConv
  have hc : Continuous fun s => g (t - s) * k s := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 R)
    (hc.intervalIntegrable R t)]
  have h1 : 0 ≤ ∫ s in R..t, g (t - s) * k s := intervalIntegral.integral_nonneg htR fun s hs =>
    mul_nonneg (hgnn _ (by linarith [hs.2])) (hknn _ (by linarith [hs.1]))
  have h2 : ∫ s in (0 : ℝ)..R, 1 / 2 * g t * k s ≤ ∫ s in (0 : ℝ)..R, g (t - s) * k s :=
    intervalIntegral.integral_mono_on hR0
      ((by fun_prop : Continuous fun s => 1 / 2 * g t * k s).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _) fun s hs => mul_le_mul_of_nonneg_right (hsh s hs) (hknn s hs.1)
  rw [intervalIntegral.integral_const_mul] at h2
  nlinarith [mul_le_mul_of_nonneg_left hRM hpt.le]

/-- **Window escape.**  For a nonnegative flat `g`, `(∫₀^t g)/g(t) → ∞`. -/
theorem tendsto_integral_div_self_atTop_of_shift {g : ℝ → ℝ} (hg : Continuous g) (hgnn : ∀ s, 0 ≤ s → 0 ≤ g s)
    (hpos : ∀ᶠ t in atTop, 0 < g t)
    (hshift : ∀ R c, 0 ≤ R → c < 1 → ∀ᶠ t in atTop, ∀ v ∈ Icc 0 R, c * g t ≤ g (t - v)) :
    Tendsto (fun t => (∫ s in (0 : ℝ)..t, g s) / g t) atTop atTop := by
  have h := tendsto_volterraConv_div_atTop hg continuous_const hgnn (fun _ _ => zero_le_one) hpos
    hshift (by
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
      exact tendsto_id)
  refine h.congr fun t => ?_
  rw [volterraConv_one_right]

/-- Differentiation of `g ⋆ k` when `k(0) = 0`: `(g ⋆ k)' = k' ⋆ g`. -/
theorem hasDerivAt_volterraConv_of_apply_zero {g k k' : ℝ → ℝ} (hk : ∀ s, HasDerivAt k (k' s) s)
    (hk' : Continuous k') (hg : Continuous g) (hk0 : k 0 = 0) (t : ℝ) :
    HasDerivAt (volterraConv g k) (volterraConv k' g t) t := by
  have h := hasDerivAt_volterraConv hk hk' hg t
  rw [hk0, zero_mul, zero_add] at h
  rwa [volterraConv_comm' g k]

/-- **Slope splitting.**  If `k'(s) ≤ εk(s)` for `s ≥ R`, then `(k' ⋆ g)(t) ≤ k(R) g(t) + ε (g ⋆ k)(t)`
for `t ≥ R`, by monotonicity of `g` on the head `[0, R]`. -/
theorem volterraConv_deriv_le {g k k' : ℝ → ℝ} (hg : Continuous g)
    (hk : ∀ s, HasDerivAt k (k' s) s) (hk' : Continuous k') (hk0 : k 0 = 0)
    (hgnn : ∀ s, 0 ≤ s → 0 ≤ g s) (hgmono : MonotoneOn g (Ici 0)) (hknn : ∀ s, 0 ≤ s → 0 ≤ k s)
    (hk'nn : ∀ s, 0 ≤ s → 0 ≤ k' s) {R ε t : ℝ} (hR : 0 ≤ R) (hRt : R ≤ t) (hε0 : 0 ≤ ε)
    (hε : ∀ s, R ≤ s → k' s ≤ ε * k s) :
    volterraConv k' g t ≤ k R * g t + ε * volterraConv g k t := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun s => (hk s).continuousAt
  rw [volterraConv_comm]
  unfold volterraConv
  have hc : Continuous fun s => g (t - s) * k' s := by fun_prop
  have hc2 : Continuous fun s => g (t - s) * k s := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 R)
    (hc.intervalIntegrable R t)]
  have h1 : ∫ s in (0 : ℝ)..R, g (t - s) * k' s ≤ ∫ s in (0 : ℝ)..R, g t * k' s :=
    intervalIntegral.integral_mono_on hR (hc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => g t * k' s).intervalIntegrable _ _) fun s hs =>
      mul_le_mul_of_nonneg_right
        (hgmono (show t - s ∈ Ici 0 by simp only [mem_Ici]; linarith [hs.2])
          (show t ∈ Ici 0 by simp only [mem_Ici]; linarith) (by linarith [hs.1]))
        (hk'nn s hs.1)
  have hFTC : ∫ s in (0 : ℝ)..R, k' s = k R - k 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hk s) (hk'.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, hFTC, hk0, sub_zero] at h1
  have h2 : ∫ s in R..t, g (t - s) * k' s ≤ ∫ s in R..t, ε * (g (t - s) * k s) :=
    intervalIntegral.integral_mono_on hRt (hc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => ε * (g (t - s) * k s)).intervalIntegrable _ _)
      fun s hs => by
        have h3 := hε s hs.1
        have h4 := hgnn (t - s) (by linarith [hs.2])
        nlinarith
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 : ∫ s in R..t, g (t - s) * k s ≤ ∫ s in (0 : ℝ)..t, g (t - s) * k s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc2.intervalIntegrable 0 R)
      (hc2.intervalIntegrable R t)]
    have : 0 ≤ ∫ s in (0 : ℝ)..R, g (t - s) * k s := intervalIntegral.integral_nonneg hR
      fun s hs => mul_nonneg (hgnn _ (by linarith [hs.2])) (hknn _ hs.1)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hε0]

/-- **Slope propagation.**  A nonnegative nondecreasing `g` with `(g ⋆ k)/g → ∞`, convolved with
`k ≥ 0`, `k(0) = 0`, `k' ≥ 0`, `k'/k → 0`, gives `(k' ⋆ g)/(g ⋆ k) → 0`. -/
theorem tendsto_volterraConv_slope_zero {g k k' : ℝ → ℝ} (hg : Continuous g)
    (hk : ∀ s, HasDerivAt k (k' s) s) (hk' : Continuous k') (hk0 : k 0 = 0)
    (hgnn : ∀ s, 0 ≤ s → 0 ≤ g s) (hgmono : MonotoneOn g (Ici 0)) (hkpos : ∀ s, 0 < s → 0 < k s)
    (hk'nn : ∀ s, 0 ≤ s → 0 ≤ k' s) (hgpos : ∀ᶠ t in atTop, 0 < g t)
    (hratio : Tendsto (fun t => volterraConv g k t / g t) atTop atTop)
    (hkslope : Tendsto (fun s => k' s / k s) atTop (𝓝 0)) :
    Tendsto (fun t => volterraConv k' g t / volterraConv g k t) atTop (𝓝 0) := by
  have hknn : ∀ s, 0 ≤ s → 0 ≤ k s := fun s hs => by
    rcases hs.eq_or_lt with rfl | hs
    · rw [hk0]
    · exact (hkpos s hs).le
  have hk'c : Continuous k' := hk'
  have hFpos : ∀ᶠ t in atTop, 0 < volterraConv g k t := by
    filter_upwards [hratio.eventually (eventually_gt_atTop 0), hgpos] with t h1 h2
    exact (div_pos_iff_of_pos_right h2).1 h1
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hFpos, eventually_ge_atTop 0] with t hF ht
    exact ha.trans_le (div_nonneg (volterraConv_nonneg_of_nonneg ht (fun s hs => hk'nn s hs.1)
      (fun s hs => hgnn s hs.1)) hF.le)
  · intro a ha
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hkslope.eventually (gt_mem_nhds (half_pos ha)))
    set R := max R₀ 1
    have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
    have hε : ∀ s, R ≤ s → k' s ≤ a / 2 * k s := fun s hs => by
      have hs1 : 0 < s := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hs)
      have h := hR₀ s ((le_max_left _ _).trans hs)
      rw [div_lt_iff₀ (hkpos s hs1)] at h
      exact h.le
    have hkR : 0 ≤ k R := hknn R hR
    filter_upwards [hFpos, hgpos, eventually_ge_atTop R,
      hratio.eventually (eventually_gt_atTop (2 * k R / a))] with t hF hgt htR hrat
    have hb := volterraConv_deriv_le hg hk hk' hk0 hgnn hgmono hknn hk'nn hR htR (half_pos ha).le hε
    rw [div_lt_iff₀ hF]
    rw [lt_div_iff₀ hgt] at hrat
    have : k R * g t < a / 2 * volterraConv g k t := by
      have := mul_lt_mul_of_pos_left hrat (half_pos ha)
      field_simp at this ⊢
      nlinarith
    nlinarith

end

end GaloisForLFunctions.HTGeometry
