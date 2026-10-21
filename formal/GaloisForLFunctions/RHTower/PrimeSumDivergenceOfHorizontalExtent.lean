import GaloisForLFunctions.RHTower.ExponentialTypeNotSummableOnPrimeLogsCapFree

/-!
# Prime-log divergence governed by the horizontal extent only

Let `Φ ≢ 0` be entire of exponential type (`‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` for some `ρ`), and suppose that on
the negative real ray `‖Φ(−x)‖ ≤ A e^{bx}`.  Then for `0 ≤ σ` and `b < 1 − σ` the partial sums
`Σ_{p<N} p^{−σ}‖Φ(log p)‖` are unbounded (`exists_primeLogWeightedSum_gt_of_negRay`).

The cap-free lemma `exists_primeLogWeightedSum_gt_of_lt_one_sub_capFree` needs `ρ < 1 − σ`
because its floor for the ray exponent `a = h(0)` is `a ≥ −ρ`, obtained from the two-ray theorem
with the full type.  Here the floor is `a ≥ −b` (`neg_le_rayExponent_of_negRay`): an admissible
exponent `a < −b` makes `Φ(w) e^{κw}`, `κ = (b − a)/2`, decay like `e^{−ε|t|}` on both real rays
(`ε = (−b − a)/2`), so `Φ` vanishes.  The Phragmén–Lindelöf thin-strip bound and the window
assembly are unchanged; the exponential type, which measures the vertical extent of the pairing's
support, enters only through constants.  This is what makes the lemma usable for Hilbert spaces
on regions of large vertical extent, such as finite unions of discs covering a compact set of
the strip.
-/

open Complex Filter Topology Set Finset Metric MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-! ## The ray-exponent floor from the negative-ray rate -/

/-- **No admissible exponent lies below `−b`** when `‖Φ(−x)‖ ≤ A e^{bx}` on the negative ray:
an exponent `a < −b` makes `Φ(w) e^{κw}`, `κ = b + ε`, `ε = (−b − a)/2`, decay like `e^{−ε|t|}` on
both real rays, so `Φ` vanishes by the two-ray theorem. -/
theorem neg_le_of_mem_rayExponentSet_of_negRay {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 < C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    (hne : Φ ≠ 0) {A b : ℝ}
    (hneg : ∀ x : ℝ, 0 ≤ x → ‖Φ ((-x : ℝ) : ℂ)‖ ≤ A * Real.exp (b * x))
    {a : ℝ} (ha : a ∈ rayExponentSet Φ) : -b ≤ a := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t₀', ht₀'⟩ := ha
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = max t₀' 0 := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; exact le_max_right _ _
  have hup : ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp (a * t) := fun t ht =>
    ht₀' t (le_trans (by rw [ht₀]; exact le_max_left _ _) ht)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (-b - a) / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = b + ε := ⟨_, rfl⟩
  -- the damped function
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun w => Φ w * cexp ((κ : ℂ) * w) := ⟨_, rfl⟩
  have hgd : Differentiable ℂ g := by
    rw [hg]
    exact hΦ.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hgnorm : ∀ w : ℂ, ‖g w‖ = ‖Φ w‖ * Real.exp (κ * w.re) := fun w => by
    rw [hg]
    simp only [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ,
      C' = max A (max 1 (C * Real.exp ((ρ + |κ| + ε) * t₀))) := ⟨_, rfl⟩
  have hC'1 : 1 ≤ C' := by
    rw [hC']
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAC' : A ≤ C' := by rw [hC']; exact le_max_left _ _
  have hCC' : C * Real.exp ((ρ + |κ| + ε) * t₀) ≤ C' := by
    rw [hC']
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- global growth of `g`: the type is at most `ρ + |κ|`
  have hgrow' : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp ((ρ + |κ|) * ‖z‖) := fun z => by
    rw [hgnorm]
    have h1 : κ * z.re ≤ |κ| * ‖z‖ := by
      calc κ * z.re ≤ |κ * z.re| := le_abs_self _
        _ = |κ| * |z.re| := abs_mul _ _
        _ ≤ |κ| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)
    calc ‖Φ z‖ * Real.exp (κ * z.re) ≤ C * Real.exp (ρ * ‖z‖) * Real.exp (|κ| * ‖z‖) :=
          mul_le_mul (hgrow z) (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp ((ρ + |κ|) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  -- decay on the positive ray: `a + κ = −ε`
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖g (x : ℂ)‖ ≤ C' * Real.exp (-(ε * x)) := by
    intro x hx
    rw [hgnorm, Complex.ofReal_re]
    rcases le_or_gt t₀ x with hxt | hxt
    · calc ‖Φ (x : ℂ)‖ * Real.exp (κ * x) ≤ Real.exp (a * x) * Real.exp (κ * x) :=
            mul_le_mul_of_nonneg_right (hup x hxt) (Real.exp_pos _).le
        _ = Real.exp (-(ε * x)) := by
            rw [← Real.exp_add]
            congr 1
            rw [hκ, hε]
            ring
        _ ≤ C' * Real.exp (-(ε * x)) :=
            le_mul_of_one_le_left (Real.exp_pos _).le hC'1
    · have h1 : ‖Φ (x : ℂ)‖ ≤ C * Real.exp (ρ * x) := by
        have := hgrow (x : ℂ)
        rwa [Complex.norm_real, Real.norm_of_nonneg hx] at this
      have hκx : κ * x ≤ |κ| * x := mul_le_mul_of_nonneg_right (le_abs_self κ) hx
      calc ‖Φ (x : ℂ)‖ * Real.exp (κ * x) ≤ C * Real.exp (ρ * x) * Real.exp (|κ| * x) :=
            mul_le_mul h1 (Real.exp_le_exp.mpr hκx) (Real.exp_pos _).le (by positivity)
        _ = C * Real.exp ((ρ + |κ| + ε) * x) * Real.exp (-(ε * x)) := by
            rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
        _ ≤ C * Real.exp ((ρ + |κ| + ε) * t₀) * Real.exp (-(ε * x)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left hxt.le (by positivity))) hC.le) (Real.exp_pos _).le
        _ ≤ C' * Real.exp (-(ε * x)) := mul_le_mul_of_nonneg_right hCC' (Real.exp_pos _).le
  -- decay on the negative ray: `κ − b = ε`
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g (x : ℂ)‖ ≤ C' * Real.exp (ε * x) := by
    intro x hx
    rw [hgnorm, Complex.ofReal_re]
    have h1 : ‖Φ (x : ℂ)‖ ≤ A * Real.exp (b * (-x)) := by
      have := hneg (-x) (by linarith)
      rwa [neg_neg] at this
    calc ‖Φ (x : ℂ)‖ * Real.exp (κ * x) ≤ A * Real.exp (b * (-x)) * Real.exp (κ * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = A * Real.exp (ε * x) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          rw [hκ]
          ring
      _ ≤ C' * Real.exp (ε * x) := mul_le_mul_of_nonneg_right hAC' (Real.exp_pos _).le
  have hzero := eq_zero_of_two_ray_exponential_decay hgd hC.le (by positivity) hε0 hgrow' hplus
    hminus
  apply hne
  funext w
  have := congrFun hzero w
  rw [hg] at this
  simp only [Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  exact this

/-- **The ray exponent is at least `−b`** when `‖Φ(−x)‖ ≤ A e^{bx}` on the negative ray. -/
theorem neg_le_rayExponent_of_negRay {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ}
    (hC : 0 < C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0)
    {A b : ℝ}
    (hneg : ∀ x : ℝ, 0 ≤ x → ‖Φ ((-x : ℝ) : ℂ)‖ ≤ A * Real.exp (b * x)) :
    -b ≤ rayExponent Φ :=
  le_csInf (rayExponentSet_nonempty hC hgrow)
    fun _ ha => neg_le_of_mem_rayExponentSet_of_negRay hΦ hC hρ hgrow hne hneg ha

/-! ## The prime sums are unbounded whenever `b < 1 − σ` -/

/-- **The prime-sum lower bound governed by the negative-ray rate.**  For `Φ ≢ 0` entire with
`‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` and `‖Φ(−x)‖ ≤ A e^{bx}` for `x ≥ 0`, `0 ≤ σ` and `b < 1 − σ`, the sums
`Σ_{p<N} p^{−σ} ‖Φ(log p)‖` are unbounded.  The exponential type `ρ` is arbitrary. -/
theorem exists_primeLogWeightedSum_gt_of_negRay {Φ : ℂ → ℂ}
    (hΦ : Differentiable ℂ Φ) {C ρ σ A b : ℝ} (hρ : 0 ≤ ρ)
    (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0) (hσ : 0 ≤ σ)
    (hneg : ∀ x : ℝ, 0 ≤ x → ‖Φ ((-x : ℝ) : ℂ)‖ ≤ A * Real.exp (b * x))
    (hb : b < 1 - σ) (M : ℝ) :
    ∃ N : ℕ, M < primeLogWeightedSum Φ σ N := by
  -- the growth constant is positive, since `Φ ≢ 0`
  have hC : 0 < C := by
    by_contra hC
    simp only [not_lt] at hC
    apply hne
    funext ξ
    have h := hgrow ξ
    have h2 : C * Real.exp (ρ * ‖ξ‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    exact norm_le_zero_iff.mp (le_trans h h2)
  -- the small exponent `δ`
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ 8 * δ ≤ 1 - σ - b ∧ δ ≤ 1 / 20 :=
    ⟨min ((1 - σ - b) / 8) (1 / 20), lt_min (by linarith) (by norm_num),
      by linarith [min_le_left ((1 - σ - b) / 8) (1 / 20)], min_le_right _ _⟩
  -- the ray exponent `a ≥ −b` and the admissible exponent `a' = a + δ`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = rayExponent Φ := ⟨_, rfl⟩
  have ha_lo : -b ≤ a := by
    rw [ha]
    exact neg_le_rayExponent_of_negRay hΦ hC hρ hgrow hne hneg
  obtain ⟨t₀, ht₀0, hup⟩ := exists_forall_norm_le_exp_rayExponent_add hC hgrow hδ0
  rw [← ha] at hup
  -- the thin-strip bound and the Lipschitz constant `K₀ e^{(a+δ)x}`
  obtain ⟨M₁, hM₁0, hstrip⟩ := exists_thinStrip_bound hΦ hC hρ hgrow ht₀0 hup
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = M₁ * Real.exp (3 * |a + δ|) := ⟨_, rfl⟩
  have hK₀0 : 0 < K₀ := by rw [hK₀]; positivity
  have hlipK : ∀ x u v : ℝ, 1 ≤ x → x ≤ u → u ≤ v → v ≤ x + 2 →
      ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ K₀ * Real.exp ((a + δ) * x) * (v - u) := by
    intro x u v hx hu huv hv
    rw [hK₀]
    exact norm_sub_le_of_thinStrip hΦ hM₁0.le hstrip hx hu huv hv
  -- the window theorem at exponent `α = 1 − 7δ`
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - 7 * δ := ⟨_, rfl⟩
  have hα7 : 7 / 12 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hα0 : 0 ≤ α := by linarith
  obtain ⟨X₁, -, hθ⟩ := exists_theta_window_lower_seven_twelfths hα7 hα1
  -- the window-length constant `c₀ = 1/(8K₀ + 1)`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 / (8 * K₀ + 1) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hc₀1 : c₀ ≤ 1 := by
    rw [hc₀, div_le_one (by positivity)]
    linarith
  have hc₀K : c₀ * K₀ ≤ 1 / 8 := by
    rw [hc₀, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the thresholds
  have hev : ∀ᶠ x : ℝ in atTop, t₀ ≤ x ∧ 1 ≤ x ∧ X₁ ≤ Real.exp x ∧
      2 * K₀ ≤ Real.exp (δ * x) ∧ 4 * Real.exp (1 - 7 * δ) / c₀ ≤ Real.exp (δ * x) ∧
      (M + 1) * 16 * Real.exp σ ≤ 2 * δ * Real.exp (2 * δ * x) := by
    have h1 : Tendsto (fun x : ℝ => Real.exp (δ * x)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hδ0)
    have h2 : Tendsto (fun x : ℝ => 2 * δ * Real.exp (2 * δ * x)) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))).const_mul_atTop
        (by linarith)
    refine (eventually_ge_atTop t₀).and ((eventually_ge_atTop 1).and
      ((Real.tendsto_exp_atTop.eventually_ge_atTop X₁).and
      ((h1.eventually_ge_atTop _).and ((h1.eventually_ge_atTop _).and
      (h2.eventually_ge_atTop _)))))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  -- a large point where `Φ` is large at the ray exponent
  obtain ⟨x, hxT, hbig⟩ := exists_exp_rayExponent_sub_lt hΦ hC hρ hgrow hne hδ0 T
  rw [← ha] at hbig
  obtain ⟨hxt₀, hx1, hxX₁, hxK, hxc, hxM⟩ := hT x hxT
  have hx0 : 0 ≤ x := by linarith
  -- the Lipschitz constant on `[x, x+2]`
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = K₀ * Real.exp ((a + δ) * x) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hlip : ∀ u v : ℝ, x ≤ u → u ≤ v → v ≤ x + 2 →
      ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ D * (v - u) := fun u v hu huv hv => by
    rw [hD]; exact hlipK x u v hx1 hu huv hv
  -- the window `[x, x + ℓ]`, `ℓ = e^{−3δx}`, on which `Φ` stays above `½ e^{(a−δ)x}`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.exp (-(3 * δ * x)) := ⟨_, rfl⟩
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact Real.exp_pos _
  have hδx : 0 ≤ δ * x := mul_nonneg hδ0.le hx0
  have hℓ1 : ℓ ≤ 1 := by rw [hℓ]; exact Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ℝ, v₀ = Real.exp ((a - δ) * x) := ⟨_, rfl⟩
  have hv₀0 : 0 < v₀ := by rw [hv₀]; exact Real.exp_pos _
  have hDℓ : D * ℓ ≤ v₀ / 2 := by
    rw [hD, hℓ, hv₀, mul_assoc, ← Real.exp_add]
    have h1 : Real.exp ((a + δ) * x + -(3 * δ * x)) = Real.exp ((a - δ) * x) * Real.exp (-(δ * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]
    have h2 : K₀ * Real.exp (-(δ * x)) ≤ 1 / 2 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    calc K₀ * (Real.exp ((a - δ) * x) * Real.exp (-(δ * x)))
        = (K₀ * Real.exp (-(δ * x))) * Real.exp ((a - δ) * x) := by ring
      _ ≤ 1 / 2 * Real.exp ((a - δ) * x) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp ((a - δ) * x) / 2 := by ring
  have hwindow : ∀ t : ℝ, 0 ≤ t → t ≤ ℓ → v₀ / 2 ≤ ‖Φ (x + t)‖ := by
    intro t ht0 htℓ
    have hsub := hlip x (x + t) le_rfl (by linarith) (by linarith)
    rw [Complex.ofReal_add] at hsub
    have h1 := norm_sub_norm_le (Φ (x : ℂ)) (Φ ((x : ℂ) + (t : ℂ)))
    rw [norm_sub_rev] at h1
    have h2 : D * (x + t - x) ≤ D * ℓ := by gcongr; linarith
    have h3 : v₀ < ‖Φ (x : ℂ)‖ := by rw [hv₀]; exact hbig
    linarith
  -- the window integral
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ℓ * (v₀ / 2) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hmint : m ≤ ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ := by
    have hcont : Continuous fun t : ℝ => ‖Φ (x + t)‖ :=
      (hΦ.continuous.comp (continuous_const.add continuous_ofReal)).norm
    have hint1 : ∫ t in (0 : ℝ)..ℓ, ‖Φ (x + t)‖ ≤ ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ :=
      intervalIntegral.integral_mono_interval le_rfl hℓ0.le hℓ1
        (Eventually.of_forall fun t => norm_nonneg _) (hcont.intervalIntegrable _ _)
    have hint2 : ∫ t in (0 : ℝ)..ℓ, v₀ / 2 ≤ ∫ t in (0 : ℝ)..ℓ, ‖Φ (x + t)‖ :=
      intervalIntegral.integral_mono_on hℓ0.le (continuous_const.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) fun t ht => hwindow t ht.1 ht.2
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint2
    rw [hm]
    linarith
  -- the window count `N` and the window length `h = 1/N`
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = c₀ * Real.exp (-(6 * δ * x)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by
    rw [hη]
    calc c₀ * Real.exp (-(6 * δ * x)) ≤ 1 * 1 :=
          mul_le_mul hc₀1 (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le zero_le_one
      _ = 1 := mul_one 1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈1 / η⌉₊ := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / N := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hh]; field_simp
  have hhη : h ≤ η := by
    rw [hh, div_le_iff₀ (by positivity)]
    have h1 := Nat.le_ceil (1 / η)
    rw [← hN] at h1
    calc (1 : ℝ) = 1 / η * η := by field_simp
      _ ≤ N * η := mul_le_mul_of_nonneg_right h1 hη0.le
      _ = η * N := mul_comm _ _
  have hηh : η / 2 ≤ h := by
    rw [hh, le_div_iff₀ (by positivity)]
    have h1 : (N : ℝ) < 1 / η + 1 := by rw [hN]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) / η + 1 ≤ 2 / η := by
      rw [div_add_one hη0.ne', div_le_div_iff_of_pos_right hη0]
      linarith
    calc η / 2 * N ≤ η / 2 * (2 / η) := by gcongr; linarith
      _ = 1 := by field_simp
  -- the Lipschitz constraint `hD ≤ m/4`
  have hhD : h * D ≤ m / 4 := by
    calc h * D ≤ η * D := mul_le_mul_of_nonneg_right hhη hD0
      _ = c₀ * K₀ * (Real.exp (-(6 * δ * x)) * Real.exp ((a + δ) * x)) := by
          rw [hη, hD]; ring
      _ = c₀ * K₀ * (Real.exp (-(δ * x)) * Real.exp ((a - 4 * δ) * x)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ ≤ 1 / 8 * (1 * Real.exp ((a - 4 * δ) * x)) := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = m / 4 := by
          rw [hm, hℓ, hv₀, show Real.exp ((a - 4 * δ) * x)
            = Real.exp (-(3 * δ * x)) * Real.exp ((a - δ) * x) by
              rw [← Real.exp_add]; congr 1; ring]
          ring
  -- the short-interval condition `e^{(x+1)α} ≤ e^x h/2`
  have hα : Real.exp (x + 1) ^ α ≤ Real.exp x * h / 2 := by
    rw [← Real.exp_mul, hαdef]
    have h1 : Real.exp ((x + 1) * (1 - 7 * δ)) = Real.exp (1 - 7 * δ) * Real.exp x * Real.exp (-(7 * δ * x)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [h1]
    have h2 : Real.exp x * h / 2 ≥ Real.exp x * (η / 4) := by
      have := mul_le_mul_of_nonneg_left hηh (Real.exp_pos x).le
      linarith
    have h3 : Real.exp (1 - 7 * δ) * Real.exp (-(7 * δ * x)) ≤ c₀ / 4 * Real.exp (-(6 * δ * x)) := by
      have h4 : Real.exp (-(7 * δ * x)) = Real.exp (-(δ * x)) * Real.exp (-(6 * δ * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      rw [div_le_iff₀ hc₀0] at hxc
      linarith
    calc Real.exp (1 - 7 * δ) * Real.exp x * Real.exp (-(7 * δ * x))
        = Real.exp x * (Real.exp (1 - 7 * δ) * Real.exp (-(7 * δ * x))) := by ring
      _ ≤ Real.exp x * (c₀ / 4 * Real.exp (-(6 * δ * x))) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = Real.exp x * (η / 4) := by rw [hη]; ring
      _ ≤ Real.exp x * h / 2 := h2
  -- the size condition
  have hM : M + 1 ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1)) * (m / 2) := by
    have hx1' : (0 : ℝ) < x + 1 := by linarith
    have hm2 : m / 2 = 1 / 4 * Real.exp ((a - 4 * δ) * x) := by
      rw [hm, hℓ, hv₀, show Real.exp ((a - 4 * δ) * x)
        = Real.exp (-(3 * δ * x)) * Real.exp ((a - δ) * x) by
          rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [hm2]
    have h1 : Real.exp (-(σ * (x + 1))) * Real.exp x * Real.exp ((a - 4 * δ) * x)
        = Real.exp (-σ) * Real.exp ((1 - σ + a - 4 * δ) * x) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (4 * δ * x) ≤ Real.exp ((1 - σ + a - 4 * δ) * x) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_nonneg (show 0 ≤ 1 - σ + a - 8 * δ by linarith) hx0
      linarith
    have h3 : 2 * δ * (x + 1) ≤ Real.exp (2 * δ * x) := by
      have := Real.add_one_le_exp (2 * δ * x)
      linarith
    have h4 : Real.exp (4 * δ * x) = Real.exp (2 * δ * x) * Real.exp (2 * δ * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h5 : (M + 1) * 16 * Real.exp σ * (x + 1) ≤ Real.exp (4 * δ * x) := by
      rw [h4]
      calc (M + 1) * 16 * Real.exp σ * (x + 1) ≤ 2 * δ * Real.exp (2 * δ * x) * (x + 1) :=
            mul_le_mul_of_nonneg_right hxM hx1'.le
        _ = Real.exp (2 * δ * x) * (2 * δ * (x + 1)) := by ring
        _ ≤ Real.exp (2 * δ * x) * Real.exp (2 * δ * x) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    have hexpσ : Real.exp (-σ) * Real.exp σ = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hQ : Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1))
          * (1 / 4 * Real.exp ((a - 4 * δ) * x))
        = Real.exp (-σ) * Real.exp ((1 - σ + a - 4 * δ) * x) / (16 * (x + 1)) := by
      rw [← h1]
      field_simp
      ring
    rw [hQ, le_div_iff₀ (by positivity)]
    calc (M + 1) * (16 * (x + 1)) = Real.exp (-σ) * ((M + 1) * 16 * Real.exp σ * (x + 1)) := by
          rw [show Real.exp (-σ) * ((M + 1) * 16 * Real.exp σ * (x + 1))
              = (Real.exp (-σ) * Real.exp σ) * ((M + 1) * (16 * (x + 1))) by ring, hexpσ, one_mul]
      _ ≤ Real.exp (-σ) * Real.exp (4 * δ * x) :=
          mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      _ ≤ Real.exp (-σ) * Real.exp ((1 - σ + a - 4 * δ) * x) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  exact exists_primeLogWeightedSum_gt_of_window_data_lip hΦ hσ hx0 hh0 hN0 hNh hD0 hlip hθ hα0
    hxX₁ hα hmint hhD hM

end RHTower
