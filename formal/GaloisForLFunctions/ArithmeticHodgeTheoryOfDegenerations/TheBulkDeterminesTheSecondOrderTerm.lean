import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimesOfAHorizonWindow

/-!
# The bulk determines the second-order term

The rescaled limit of the bulk is the first-order structure of the degeneration:
`s^β E₁(s) → J`, `J` the conductor-one Jordan coefficient. The second-order term of a horizon
window is Weil's form plus `log N` times the window average of `−E₁'` at the local overlaps. This
file shows that the first determines the second, for every profile:

* **Regularity of the aliasing density** (`abs_aliasDensity_sub_le`, `aliasDensity_le`): for
  `|φ̂(u)|² ≤ C_φ(1 + |u|)^{−p}`, `p > 4`, the density is bounded and Lipschitz on `[s₀, ∞)`.
* **Integration by parts against the bulk** (`integral_logProfile_mul_aliasDensity`): on a window,
  `∫ F(x) a_φ(cx) dx = (∫φ²/2c) ∫ F'(x) E₁(cx) dx`, so the window average of the aliasing is an
  average of the bulk energy itself.
* **The second-order term** (`horizon_layer_criticalCurve_of_regularBulk`): if `s^β E₁(s) → J`,
  then along `c^{β+1}/log N → K`,

  `c⁻¹ ⟨W x, x⟩ → κ Q(H) + (β J/K) ∫ e^{−(β+1)y} H(y)² dy`.

The constant is `β J`: the pointwise density of the bulk limit `J s^{−β}` under dilation. No
property of the profile beyond its first-order limit and decay enters. For the tilted spline,
`β = 7` and `J = J(1)`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticCastelnuovoSeveri

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### Regularity of the aliasing density -/

/-- The transform is `∫|φ|`-Lipschitz on the real line: `|φ̂(x) − φ̂(x')| ≤ |x − x'| ∫|φ|`. -/
theorem norm_paperFT_sub_le (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x x' : ℝ) : ‖paperFT (cx φ) (x : ℂ) - paperFT (cx φ) (x' : ℂ)‖ ≤ |x - x'| * ∫ u, |φ u| := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hi : ∀ z : ℂ, Integrable fun u : ℝ => cx φ u * Complex.exp (Complex.I * z * u) := by
    intro z
    refine Continuous.integrable_of_hasCompactSupport (by unfold cx; fun_prop) ?_
    exact (hφc.comp_left Complex.ofReal_zero).mul_right
  rw [paperFT_def, paperFT_def, ← integral_sub (hi _) (hi _), ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) ((hφ.abs.integrable_of_hasCompactSupport
      hφc.abs).const_mul _) (Eventually.of_forall fun u => ?_))
  simp only [cx]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · have he : ‖Complex.exp (Complex.I * x * u) - Complex.exp (Complex.I * x' * u)‖ ≤ |x - x'| := by
      have hsplit : Complex.exp (Complex.I * x * u) - Complex.exp (Complex.I * x' * u) =
          Complex.exp (Complex.I * x' * u) *
            (Complex.exp (Complex.I * (((x - x') * u : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 2; push_cast; ring
      rw [hsplit, norm_mul]
      have h1 : ‖Complex.exp (Complex.I * x' * u)‖ = 1 := by
        rw [show Complex.I * (x' : ℂ) * (u : ℂ) = ((x' * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (x - x') * u)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.1] at h2
      rw [h1, one_mul]
      exact h2.trans (mul_le_of_le_one_right (abs_nonneg _) hu.2)
    calc |φ u| * ‖Complex.exp (Complex.I * x * u) - Complex.exp (Complex.I * x' * u)‖
        ≤ |φ u| * |x - x'| := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = |x - x'| * |φ u| := by ring
  · rw [hφsupp u hu, abs_zero, zero_mul, mul_zero]

/-- The decay in norm: `|φ̂(u)| ≤ √C_φ (1 + |u|)^{−p/2}`. -/
theorem norm_paperFT_le_of_decay {Cφ p : ℝ} (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) (u : ℝ) :
    ‖paperFT (cx φ) u‖ ≤ Real.sqrt Cφ * (1 + |u|) ^ (-p / 2) := by
  have hb : 0 < 1 + |u| := by positivity
  have e : Real.sqrt Cφ * (1 + |u|) ^ (-p / 2) = Real.sqrt (Cφ * (1 + |u|) ^ (-p)) := by
    rw [Real.sqrt_mul hCφ, Real.sqrt_eq_rpow ((1 + |u|) ^ (-p)), ← Real.rpow_mul hb.le]
    ring_nf
  rw [e]
  exact Real.le_sqrt_of_sq_le (hdecay u)

/-- A harmonic varies slowly: for `t, t' ≥ T ≥ 0`,
`|P(t) − P(t')| ≤ 4π √C_φ (∫|φ|) (1 + 2πT)^{−p/2} |t − t'|`. -/
theorem abs_shellSpectrum_sub_le (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hCφ : 0 ≤ Cφ) (hp : 0 ≤ p)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {T t t' : ℝ} (hT : 0 ≤ T)
    (ht : T ≤ t) (ht' : T ≤ t') :
    |shellSpectrum φ t - shellSpectrum φ t'| ≤
      4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) * (1 + 2 * Real.pi * T) ^ (-p / 2) * |t - t'| := by
  have hpi := Real.pi_pos
  set a := paperFT (cx φ) ((2 * Real.pi * t : ℝ) : ℂ) with ha
  set b := paperFT (cx φ) ((2 * Real.pi * t' : ℝ) : ℂ) with hb
  have hP : ∀ s, shellSpectrum φ s = ‖paperFT (cx φ) ((2 * Real.pi * s : ℝ) : ℂ)‖ ^ 2 := fun s => rfl
  rw [hP, hP]
  have hdec : ∀ s, T ≤ s → ‖paperFT (cx φ) ((2 * Real.pi * s : ℝ) : ℂ)‖ ≤
      Real.sqrt Cφ * (1 + 2 * Real.pi * T) ^ (-p / 2) := by
    intro s hs
    refine (norm_paperFT_le_of_decay hCφ hdecay _).trans (mul_le_mul_of_nonneg_left ?_
      (Real.sqrt_nonneg _))
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  have hab := norm_paperFT_sub_le hφ hφsupp (2 * Real.pi * t) (2 * Real.pi * t')
  rw [show 2 * Real.pi * t - 2 * Real.pi * t' = 2 * Real.pi * (t - t') by ring, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hab
  rw [← ha, ← hb] at hab ⊢
  rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
  have hs := add_le_add (hdec t ht) (hdec t' ht')
  rw [← ha, ← hb] at hs
  calc |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) ≤ (2 * Real.pi * |t - t'| * ∫ u, |φ u|) *
        (Real.sqrt Cφ * (1 + 2 * Real.pi * T) ^ (-p / 2) +
          Real.sqrt Cφ * (1 + 2 * Real.pi * T) ^ (-p / 2)) :=
        mul_le_mul ((abs_norm_sub_norm_le a b).trans hab) hs (by positivity) (by positivity)
    _ = _ := by ring

theorem summable_succ_rpow {r : ℝ} (hr : r < -1) : Summable fun k : ℕ => ((k : ℝ) + 1) ^ r := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hr)
  exact h.congr fun k => by push_cast; rfl

/-- `(1 + 2π(k+1)s)^{−q} ≤ (2πs)^{−q} (k+1)^{−q}` for `q ≥ 0`, `s > 0`. -/
theorem one_add_rpow_neg_le {q s : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (k : ℕ) :
    (1 + 2 * Real.pi * (((k : ℝ) + 1) * s)) ^ (-q) ≤
      (2 * Real.pi * s) ^ (-q) * ((k : ℝ) + 1) ^ (-q) := by
  have hpi := Real.pi_pos
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)

/-- **The aliasing density is Lipschitz on `[s₀, ∞)`** for `p > 4`. -/
theorem abs_aliasDensity_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {s₀ s s' : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hs' : s₀ ≤ s') :
    |aliasDensity φ s - aliasDensity φ s'| ≤
      4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) * (2 * Real.pi * s₀) ^ (-p / 2) *
        (∑' k : ℕ, ((k : ℝ) + 1) ^ (1 - p / 2)) * |s - s'| := by
  have hpi := Real.pi_pos
  set C' := 4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) * (2 * Real.pi * s₀) ^ (-p / 2) with hC'
  have hC'0 : 0 ≤ C' := by
    have : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
    positivity
  have h1 := (hasSum_aliasDensity hφ hφsupp (lt_of_lt_of_le hs₀ hs)).1
  have h2 := (hasSum_aliasDensity hφ hφsupp (lt_of_lt_of_le hs₀ hs')).1
  have hdiff := h1.sub h2
  have hbound : ∀ k : ℕ, ‖shellSpectrum φ ((k + 1) * s) - shellSpectrum φ ((k + 1) * s')‖ ≤
      C' * |s - s'| * ((k : ℝ) + 1) ^ (1 - p / 2) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hT : (0 : ℝ) ≤ ((k : ℝ) + 1) * s₀ := by positivity
    have h := abs_shellSpectrum_sub_le hφ.continuous hφsupp hCφ (by linarith) hdecay hT
      (mul_le_mul_of_nonneg_left hs hk.le) (mul_le_mul_of_nonneg_left hs' hk.le)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hr := one_add_rpow_neg_le (q := p / 2) (by linarith) hs₀ k
    rw [show -(p / 2) = -p / 2 by ring] at hr
    rw [← mul_sub, abs_mul, abs_of_pos hk]
    have e : ((k : ℝ) + 1) ^ (1 - p / 2) = ((k : ℝ) + 1) ^ (-p / 2) * ((k : ℝ) + 1) := by
      rw [show (1 : ℝ) - p / 2 = -p / 2 + 1 by ring, Real.rpow_add hk, Real.rpow_one]
    rw [e, hC']
    have hI : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
    calc 4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) * (1 + 2 * Real.pi * (((k : ℝ) + 1) * s₀)) ^ (-p / 2) *
          (((k : ℝ) + 1) * |s - s'|)
        ≤ 4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) *
            ((2 * Real.pi * s₀) ^ (-p / 2) * ((k : ℝ) + 1) ^ (-p / 2)) * (((k : ℝ) + 1) * |s - s'|) := by
          gcongr
      _ = _ := by ring
  have hsumb : Summable fun k : ℕ => C' * |s - s'| * ((k : ℝ) + 1) ^ (1 - p / 2) :=
    (summable_succ_rpow (by linarith)).mul_left _
  have hsumn : Summable fun k : ℕ => ‖shellSpectrum φ ((k + 1) * s) - shellSpectrum φ ((k + 1) * s')‖ :=
    hsumb.of_nonneg_of_le (fun k => norm_nonneg _) hbound
  rw [← hdiff.tsum_eq, ← Real.norm_eq_abs]
  calc ‖∑' k : ℕ, (shellSpectrum φ ((k + 1) * s) - shellSpectrum φ ((k + 1) * s'))‖
      ≤ ∑' k : ℕ, ‖shellSpectrum φ ((k + 1) * s) - shellSpectrum φ ((k + 1) * s')‖ :=
        norm_tsum_le_tsum_norm hsumn
    _ ≤ ∑' k : ℕ, C' * |s - s'| * ((k : ℝ) + 1) ^ (1 - p / 2) :=
        hsumn.tsum_le_tsum hbound hsumb
    _ = C' * (∑' k : ℕ, ((k : ℝ) + 1) ^ (1 - p / 2)) * |s - s'| := by rw [tsum_mul_left]; ring

/-- **The aliasing density is bounded on `[s₀, ∞)`**. -/
theorem aliasDensity_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hp : 1 < p)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) (hCφ : 0 ≤ Cφ)
    {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    aliasDensity φ s ≤ Cφ * (2 * Real.pi * s₀) ^ (-p) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (-p) := by
  have hpi := Real.pi_pos
  have h1 := (hasSum_aliasDensity hφ hφsupp (lt_of_lt_of_le hs₀ hs)).1
  have hb : ∀ k : ℕ, shellSpectrum φ ((k + 1) * s) ≤
      Cφ * (2 * Real.pi * s₀) ^ (-p) * ((k : ℝ) + 1) ^ (-p) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h := hdecay (2 * Real.pi * ((k + 1) * s))
    have hr := one_add_rpow_neg_le (q := p) (by linarith) hs₀ k
    have hmono : (1 + |2 * Real.pi * (((k : ℝ) + 1) * s)|) ^ (-p) ≤
        (1 + 2 * Real.pi * (((k : ℝ) + 1) * s₀)) ^ (-p) := by
      rw [abs_of_nonneg (by have := lt_of_lt_of_le hs₀ hs; positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hs hk.le]) (by linarith)
    calc shellSpectrum φ ((k + 1) * s) ≤ Cφ * (1 + |2 * Real.pi * (((k : ℝ) + 1) * s)|) ^ (-p) := h
      _ ≤ Cφ * ((2 * Real.pi * s₀) ^ (-p) * ((k : ℝ) + 1) ^ (-p)) :=
          mul_le_mul_of_nonneg_left (hmono.trans hr) hCφ
      _ = _ := by ring
  have hsb : Summable fun k : ℕ => Cφ * (2 * Real.pi * s₀) ^ (-p) * ((k : ℝ) + 1) ^ (-p) :=
    (summable_succ_rpow (by linarith)).mul_left _
  rw [aliasDensity, ← tsum_mul_left]
  exact h1.summable.tsum_le_tsum hb hsb

/-! ### The window average of the aliasing -/

/-- The window aliasing `G_c(x) = h(log x)² a_φ(c max(x, e^{−A}))` (the clamp only acts where the
window weight vanishes). -/
def windowAlias (φ h : ℝ → ℝ) (A c x : ℝ) : ℝ :=
  logProfile (fun y => h y ^ 2) x * aliasDensity φ (c * max x (Real.exp (-A)))

theorem horizonAlias_eq_riemann (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (φ : ℝ → ℝ) (c : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    horizonAlias φ h c N = 2 * ((N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, windowAlias φ h A c (r / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold horizonAlias
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hx : (0 : ℝ) < r / N := div_pos hr0 hN0
  have hlog : Real.log (r / N) = Real.log r - Real.log N := Real.log_div hr0.ne' hN0.ne'
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  have hW : windowAlias φ h A c (r / N) =
      h (Real.log r - Real.log N) ^ 2 * aliasDensity φ (c * r / N) := by
    unfold windowAlias
    by_cases hw : Real.exp (-A) ≤ (r : ℝ) / N
    · rw [max_eq_left hw, logProfile, if_pos hx, hlog, show c * r / N = c * (r / N) by ring]
    · have hlt : Real.log r - Real.log N < -A := by
        rw [← hlog, Real.log_lt_iff_lt_exp hx]; exact not_le.mp hw
      have hz : h (Real.log r - Real.log N) = 0 := hsupp _ fun hm => by linarith [hm.1]
      rw [logProfile_eq_zero_of_lt hgs (not_le.mp hw), hz]; ring
  rw [hW]; ring

/-- The window aliasing is Lipschitz on `[0, 1]` with constant `L_F B_a + B_F L_a c`. -/
theorem abs_windowAlias_sub_le (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |h y ^ 2| ≤ Bg) {Lg : NNReal}
    (hLg : LipschitzWith Lg fun y => h y ^ 2) {Ba La : ℝ}
    (hBa : ∀ s, Real.exp (-A) ≤ s → aliasDensity φ s ≤ Ba)
    (hLa : ∀ s s', Real.exp (-A) ≤ s → Real.exp (-A) ≤ s' →
      |aliasDensity φ s - aliasDensity φ s'| ≤ La * |s - s'|)
    {c : ℝ} (hc : 1 ≤ c) (x x' : ℝ) :
    |windowAlias φ h A c x - windowAlias φ h A c x'| ≤
      ((Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * (La * c)) * |x - x'| := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hge : ∀ z, Real.exp (-A) ≤ c * max z (Real.exp (-A)) := fun z =>
    le_trans (le_max_right z _) (le_mul_of_one_le_left (le_trans (Real.exp_pos _).le
      (le_max_right z _)) hc)
  have hLa0 : 0 ≤ La := by
    have := hLa (Real.exp (-A)) (Real.exp (-A) + 1) le_rfl (by linarith)
    rw [sub_add_cancel_left, abs_neg, abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  have hF := abs_logProfile_sub_le hg2 hgs hA hBg hLg x x'
  have hFb := abs_logProfile_le hBg x'
  have ha0 := aliasDensity_nonneg (φ := φ) (c * max x (Real.exp (-A)))
  have hab := hBa _ (hge x)
  have hda := hLa _ _ (hge x) (hge x')
  rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < c)] at hda
  have hmax := abs_max_sub_max_le_abs x x' (Real.exp (-A))
  unfold windowAlias
  have e : logProfile (fun y => h y ^ 2) x * aliasDensity φ (c * max x (Real.exp (-A))) -
      logProfile (fun y => h y ^ 2) x' * aliasDensity φ (c * max x' (Real.exp (-A))) =
      (logProfile (fun y => h y ^ 2) x - logProfile (fun y => h y ^ 2) x') *
        aliasDensity φ (c * max x (Real.exp (-A))) + logProfile (fun y => h y ^ 2) x' *
        (aliasDensity φ (c * max x (Real.exp (-A))) - aliasDensity φ (c * max x' (Real.exp (-A)))) := by
    ring
  rw [e]
  calc _ ≤ |logProfile (fun y => h y ^ 2) x - logProfile (fun y => h y ^ 2) x'| *
        aliasDensity φ (c * max x (Real.exp (-A))) + Bg *
          |aliasDensity φ (c * max x (Real.exp (-A))) - aliasDensity φ (c * max x' (Real.exp (-A)))| := by
        refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
        · rw [abs_mul, abs_of_nonneg ha0]
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
    _ ≤ ((Lg : ℝ) * Real.exp (2 * A) * |x - x'|) * Ba + Bg * (La * (c * |x - x'|)) := by
        gcongr
        exact hda.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ c)) hLa0)
    _ = _ := by ring

/-- **Integration by parts against the bulk.** With `ℓ = e^{−A−1}`:
`∫_0^1 G_c = (∫φ²/2c) ∫_ℓ^1 F'(x) E₁(cx) dx`, `F(x) = h(log x)²`. -/
theorem integral_windowAlias_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) {c : ℝ} (hc : 0 < c) :
    ∫ x in (0 : ℝ)..1, windowAlias φ h A c x =
      (∫ u, φ u ^ 2) / (2 * c) * ∫ x in Real.exp (-A - 1)..1,
        logProfileDeriv (fun y => h y ^ 2) x * completedShellEnergy φ (c * x) := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨B, L, -, hL⟩ := exists_bound_lipschitz hg2 hgs
  have hg0 : (fun y => h y ^ 2) 0 = 0 := horizon_zero_at_zero hgs hL
  set M := ∫ u, φ u ^ 2 with hMdef
  set ℓ := Real.exp (-A - 1) with hℓ
  have hℓ0 : 0 < ℓ := Real.exp_pos _
  have hℓA : ℓ < Real.exp (-A) := Real.exp_lt_exp.mpr (by linarith)
  have hℓ1 : ℓ ≤ 1 := le_of_lt (lt_of_lt_of_le hℓA (Real.exp_le_one_iff.mpr (by linarith)))
  have hcont := continuousOn_aliasDensity hφ hφsupp
  -- windowAlias vanishes below `ℓ` and is `F(x) a(cx)` above it
  have hlow : ∀ x, x < Real.exp (-A) → windowAlias φ h A c x = 0 := fun x hx => by
    rw [windowAlias, logProfile_eq_zero_of_lt hgs hx, zero_mul]
  have hG : Continuous (windowAlias φ h A c) := by
    have hFc : Continuous (logProfile (fun y => h y ^ 2)) :=
      continuous_iff_continuousAt.mpr fun x => (hasDerivAt_logProfile hg2 hgs x).continuousAt
    refine hFc.mul ?_
    refine ContinuousOn.comp_continuous (s := Set.Ioi 0) hcont
      (continuous_const.mul (continuous_id.max continuous_const)) fun x => ?_
    exact mul_pos hc (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))
  have hsplit : ∫ x in (0 : ℝ)..1, windowAlias φ h A c x =
      ∫ x in ℓ..1, logProfile (fun y => h y ^ 2) x * aliasDensity φ (c * x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := ℓ) (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
    have h0 : ∫ x in (0 : ℝ)..ℓ, windowAlias φ h A c x = 0 := by
      rw [intervalIntegral.integral_of_le hℓ0.le]
      exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => hlow x (lt_of_le_of_lt hx.2 hℓA)
    rw [h0, zero_add]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hℓ1] at hx
    by_cases hw : Real.exp (-A) ≤ x
    · simp only [windowAlias, max_eq_left hw]
    · rw [hlow x (not_le.mp hw), logProfile_eq_zero_of_lt hgs (not_le.mp hw), zero_mul]
  -- integration by parts
  have hu : ∀ x ∈ Set.uIcc ℓ 1, HasDerivAt (logProfile (fun y => h y ^ 2))
      (logProfileDeriv (fun y => h y ^ 2) x) x := fun x _ => hasDerivAt_logProfile hg2 hgs x
  have hv : ∀ x ∈ Set.uIcc ℓ 1, HasDerivAt (fun x => completedShellEnergy φ (c * x))
      (c * (-(2 / M) * aliasDensity φ (c * x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hℓ1] at hx
    have hx0 : 0 < c * x := mul_pos hc (lt_of_lt_of_le hℓ0 hx.1)
    have := (hasDerivAt_completedShellEnergy hφ hφsupp hM hx0).comp x
      ((hasDerivAt_id x).const_mul c)
    rw [← hMdef] at this
    exact this.congr_deriv (by ring)
  have hu' : IntervalIntegrable (logProfileDeriv (fun y => h y ^ 2)) volume ℓ 1 :=
    (continuous_logProfileDeriv hg2 hgs).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x => c * (-(2 / M) * aliasDensity φ (c * x))) volume ℓ 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_const.mul ?_)
    refine hcont.comp (continuousOn_const.mul continuousOn_id) fun x hx => ?_
    rw [Set.uIcc_of_le hℓ1] at hx
    exact mul_pos hc (lt_of_lt_of_le hℓ0 hx.1)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [logProfile_eq_zero_of_one_le hgs hg0 le_rfl, logProfile_eq_zero_of_lt hgs hℓA, zero_mul,
    zero_mul, sub_zero, zero_sub] at hibp
  have hlhs : ∫ x in ℓ..1, logProfile (fun y => h y ^ 2) x * (c * (-(2 / M) * aliasDensity φ (c * x))) =
      -(2 * c / M) * ∫ x in ℓ..1, logProfile (fun y => h y ^ 2) x * aliasDensity φ (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [hlhs] at hibp
  rw [hsplit]
  have hM0 : M ≠ 0 := hM.ne'
  have hc0 : c ≠ 0 := hc.ne'
  field_simp
  field_simp at hibp
  linarith

/-- Riemann sums of a `K`-Lipschitz function on `[0, 1]`: error `≤ K/N`. -/
theorem abs_riemann_sub_le_of_lipschitz {G : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x x', |G x - G x'| ≤ K * |x - x'|) {N : ℕ} (hN : 1 ≤ N) :
    |(N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, G (r / N) - ∫ x in (0 : ℝ)..1, G x| ≤ K / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hGlip : LipschitzOnWith (Real.toNNReal K) G (Set.Icc 0 1) :=
    LipschitzOnWith.of_dist_le_mul fun u _ v _ => by
      rw [Real.coe_toNNReal _ hK, Real.dist_eq, Real.dist_eq]; exact hlip u v
  have h := RHTower.abs_riemannSum_sub_integral_le hGlip hGlip.continuousOn N (h := 1 / N)
    (by positivity) (by rw [mul_one_div, div_self hN0.ne'])
  rw [Real.coe_toNNReal _ hK, mul_one_div, div_self hN0.ne'] at h
  have hsum : ∑ i ∈ Finset.range N, G ((i + 1) * (1 / N)) = ∑ r ∈ Icc 1 N, G (r / N) := by
    rw [show Icc 1 N = Finset.Ico 1 (N + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
      show N + 1 - 1 = N by omega]
    refine sum_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  rw [hsum, show K * N * (1 / N) ^ 2 = K / N by field_simp] at h
  rw [show (N : ℝ)⁻¹ = 1 / N by ring]
  exact h

/-! ### The bulk limit on a window -/

/-- **The bulk limit on a window.** If `s^β E(s) → J`, then
`c^β ∫_ℓ^1 F'(x) E(cx) dx → J ∫_ℓ^1 F'(x) x^{−β} dx` as `c → ∞`. -/
theorem tendsto_window_bulk {E : ℝ → ℝ} {β J : ℝ}
    (hE : Tendsto (fun s => s ^ β * E s) atTop (𝓝 J)) (hEc : ContinuousOn E (Set.Ioi 0))
    {F' : ℝ → ℝ} (hF' : Continuous F') {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => c N ^ β * ∫ x in ℓ..1, F' x * E (c N * x)) atTop
      (𝓝 (J * ∫ x in ℓ..1, F' x * x ^ (-β))) := by
  set V := ∫ x in ℓ..1, |F' x| * x ^ (-β) with hV
  have hFE : ∀ N : ℕ, 0 < c N → c N ^ β * ∫ x in ℓ..1, F' x * E (c N * x) =
      ∫ x in ℓ..1, F' x * x ^ (-β) * ((c N * x) ^ β * E (c N * x)) := by
    intro N hcN
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hℓ1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hℓ hx.1
    rw [Real.mul_rpow hcN.le hx0.le, Real.rpow_neg hx0.le]
    field_simp
  have hcont : ∀ N : ℕ, 0 < c N → ContinuousOn (fun x => E (c N * x)) (Set.uIcc ℓ 1) := by
    intro N hcN
    refine hEc.comp (continuousOn_const.mul continuousOn_id) fun x hx => ?_
    rw [Set.uIcc_of_le hℓ1] at hx
    exact mul_pos hcN (lt_of_lt_of_le hℓ hx.1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (V + 1) with hδ
  have hV0 : 0 ≤ V := intervalIntegral.integral_nonneg hℓ1 fun x hx => by
    have : 0 < x := lt_of_lt_of_le hℓ hx.1
    positivity
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp hE δ hδ0
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp ((tendsto_atTop.mp hc) (max (S / ℓ) 1))
  refine ⟨N₀, fun N hN => ?_⟩
  have hcN : max (S / ℓ) 1 ≤ c N := hN₀ N hN
  have hc0 : 0 < c N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hcN)
  rw [Real.dist_eq, hFE N hc0, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · have hpt : ∀ x ∈ Set.uIcc ℓ 1, ‖F' x * x ^ (-β) * ((c N * x) ^ β * E (c N * x)) -
        J * (F' x * x ^ (-β))‖ ≤ |F' x| * x ^ (-β) * δ := by
      intro x hx
      rw [Set.uIcc_of_le hℓ1] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hℓ hx.1
      have hcx : S ≤ c N * x := by
        have h1 : S / ℓ ≤ c N := (le_max_left _ _).trans hcN
        calc S ≤ c N * ℓ := by rw [div_le_iff₀ hℓ] at h1; exact h1
          _ ≤ c N * x := mul_le_mul_of_nonneg_left hx.1 hc0.le
      have hd := hS (c N * x) hcx
      rw [Real.dist_eq] at hd
      rw [Real.norm_eq_abs, show F' x * x ^ (-β) * ((c N * x) ^ β * E (c N * x)) -
        J * (F' x * x ^ (-β)) = F' x * x ^ (-β) * ((c N * x) ^ β * E (c N * x) - J) by ring,
        abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
      exact mul_le_mul_of_nonneg_left hd.le (by positivity)
    have hint : IntervalIntegrable (fun x => |F' x| * x ^ (-β) * δ) volume ℓ 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ((hF'.abs.continuousOn).mul (continuousOn_id.rpow_const fun x hx => Or.inl ?_)).mul
        continuousOn_const
      rw [Set.uIcc_of_le hℓ1] at hx; exact (lt_of_lt_of_le hℓ hx.1).ne'
    have hb := intervalIntegral.norm_integral_le_of_norm_le hℓ1 (Eventually.of_forall
      fun x hx => hpt x (by
        rw [Set.uIcc_of_le hℓ1]
        exact Set.Ioc_subset_Icc_self hx)) hint
    rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const, ← hV] at hb
    calc _ ≤ V * δ := hb
      _ < ε := by
        rw [hδ, mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  · refine ContinuousOn.intervalIntegrable ?_
    refine ((hF'.continuousOn.mul (continuousOn_id.rpow_const fun x hx => Or.inl ?_)).mul
      ((continuousOn_const.mul continuousOn_id).rpow_const (fun x hx => Or.inl ?_) |>.mul
        (hcont N hc0)))
    · rw [Set.uIcc_of_le hℓ1] at hx; exact (lt_of_lt_of_le hℓ hx.1).ne'
    · rw [Set.uIcc_of_le hℓ1] at hx; exact (mul_pos hc0 (lt_of_lt_of_le hℓ hx.1)).ne'
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (hF'.continuousOn.mul (continuousOn_id.rpow_const fun x hx =>
      Or.inl ?_))
    rw [Set.uIcc_of_le hℓ1] at hx; exact (lt_of_lt_of_le hℓ hx.1).ne'

/-- `∫_ℓ^1 F'(x) x^{−β} dx = β ∫ e^{−βy} h(y)² dy` for `F(x) = h(log x)²`, `ℓ = e^{−A−1}`. -/
theorem integral_logProfileDeriv_mul_rpow (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (β : ℝ) :
    ∫ x in Real.exp (-A - 1)..1, logProfileDeriv (fun y => h y ^ 2) x * x ^ (-β) =
      β * ∫ y, Real.exp (-(β * y)) * h y ^ 2 := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨B, L, -, hL⟩ := exists_bound_lipschitz hg2 hgs
  have hg0 : (fun y => h y ^ 2) 0 = 0 := horizon_zero_at_zero hgs hL
  set ℓ := Real.exp (-A - 1) with hℓ
  have hℓ0 : 0 < ℓ := Real.exp_pos _
  have hℓA : ℓ < Real.exp (-A) := Real.exp_lt_exp.mpr (by linarith)
  have hℓ1 : ℓ ≤ 1 := le_of_lt (lt_of_lt_of_le hℓA (Real.exp_le_one_iff.mpr (by linarith)))
  have hpos : ∀ x ∈ Set.uIcc ℓ 1, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hℓ1] at hx; exact lt_of_lt_of_le hℓ0 hx.1
  have hu : ∀ x ∈ Set.uIcc ℓ 1, HasDerivAt (logProfile (fun y => h y ^ 2))
      (logProfileDeriv (fun y => h y ^ 2) x) x := fun x _ => hasDerivAt_logProfile hg2 hgs x
  have hv : ∀ x ∈ Set.uIcc ℓ 1, HasDerivAt (fun x : ℝ => x ^ (-β)) (-β * x ^ (-β - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')
  have hu' : IntervalIntegrable (logProfileDeriv (fun y => h y ^ 2)) volume ℓ 1 :=
    (continuous_logProfileDeriv hg2 hgs).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => -β * x ^ (-β - 1)) volume ℓ 1 :=
    (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl (hpos x hx).ne')).intervalIntegrable
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [logProfile_eq_zero_of_one_le hgs hg0 le_rfl, logProfile_eq_zero_of_lt hgs hℓA, zero_mul,
    zero_mul, sub_zero, zero_sub] at hibp
  -- the remaining integral is a window integral of `h² e^{−(β+1)y}`
  set g3 : ℝ → ℝ := fun y => h y ^ 2 * Real.exp (-((β + 1) * y)) with hg3
  have hg3c : ContDiff ℝ 2 g3 :=
    hg2.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)
  have hg3s : ∀ y, y ∉ Set.Icc (-A) 0 → g3 y = 0 := fun y hy => by simp [hg3, hsupp y hy]
  have hpt : ∀ x ∈ Set.uIcc ℓ 1, logProfile (fun y => h y ^ 2) x * (-β * x ^ (-β - 1)) =
      -β * logProfile g3 x := by
    intro x hx
    have hx0 := hpos x hx
    rw [logProfile, logProfile, if_pos hx0, if_pos hx0, Real.rpow_def_of_pos hx0]
    simp only [hg3]
    rw [show Real.log x * (-β - 1) = -((β + 1) * Real.log x) by ring]
    ring
  have hlo : ∫ x in (0 : ℝ)..ℓ, logProfile g3 x = 0 := by
    rw [intervalIntegral.integral_of_le hℓ0.le]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      logProfile_eq_zero_of_lt hg3s (lt_of_le_of_lt hx.2 hℓA)
  have hG3 : Continuous (logProfile g3) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_logProfile hg3c hg3s x).continuousAt
  have hfull := integral_logProfile hg3c hg3s hA
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := ℓ) (hG3.intervalIntegrable _ _)
    (hG3.intervalIntegrable _ _), hlo, zero_add] at hfull
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, hfull] at hibp
  have hR : ∫ y, Real.exp y * g3 y = ∫ y, Real.exp (-(β * y)) * h y ^ 2 := by
    congr 1; funext y
    simp only [hg3]
    rw [show Real.exp y * (h y ^ 2 * Real.exp (-((β + 1) * y))) =
      (Real.exp y * Real.exp (-((β + 1) * y))) * h y ^ 2 by ring, ← Real.exp_add]
    congr 2; ring
  rw [hR] at hibp
  linarith

/-- Along `c^q/log N → K`, `q ≥ 1`: `c → ∞`, `c (log N)²/N → 0` and `c^{q+1}/N → 0`. -/
theorem criticalCurve_facts_rpow {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {q K : ℝ} (hq : 1 ≤ q)
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ q / Real.log N) atTop (𝓝 K)) :
    Tendsto c atTop atTop ∧ Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => c N ^ (q + 1) / N) atTop (𝓝 0) := by
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcq : Tendsto (fun N : ℕ => c N ^ q) atTop atTop := by
    have := Tendsto.pos_mul_atTop hK hcrit hlogN
    refine this.congr' ?_
    filter_upwards [hlogN.eventually (eventually_gt_atTop 0)] with N hN
    simp only [Function.comp_apply] at hN ⊢
    field_simp
  have hev : ∀ᶠ N : ℕ in atTop, c N ^ q ≤ 2 * K * Real.log N := by
    filter_upwards [hcrit.eventually (gt_mem_nhds (by linarith : K < 2 * K)),
      hlogN.eventually (eventually_gt_atTop 0)] with N h1 h2
    simp only [Function.comp_apply] at h2
    rw [div_lt_iff₀ h2] at h1
    linarith
  have hcle : ∀ N, c N ≤ c N ^ q := fun N => by
    calc c N = c N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ c N ^ q := Real.rpow_le_rpow_of_exponent_le (hc1 N) hq
  refine ⟨?_, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro B
    filter_upwards [hcq.eventually (eventually_ge_atTop (max B 1 ^ q))] with N hN
    have hc0 : 0 ≤ c N := by linarith [hc1 N]
    have : max B 1 ≤ c N :=
      (Real.rpow_le_rpow_iff (by positivity) hc0 (by linarith)).mp hN
    exact (le_max_left B 1).trans this
  · have hlim := (tendsto_log_pow_div_natCast 3).const_mul (2 * K)
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun N => by
      have := hc1 N; have := Real.log_natCast_nonneg N; positivity) ?_ hlim
    filter_upwards [hev, eventually_ge_atTop 1] with N h1 hN
    have hl0 := Real.log_natCast_nonneg N
    calc c N * Real.log N ^ 2 / N ≤ (2 * K * Real.log N) * Real.log N ^ 2 / N := by
          gcongr; exact (hcle N).trans h1
      _ = 2 * K * (Real.log N ^ 3 / N) := by ring
  · have hlim := (tendsto_log_pow_div_natCast 2).const_mul ((2 * K) ^ 2)
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun N => by
      have := hc1 N; positivity) ?_ hlim
    filter_upwards [hev, eventually_ge_atTop 1] with N h1 hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hq0 : 0 ≤ c N ^ q := by positivity
    calc c N ^ (q + 1) / N = c N * c N ^ q / N := by
          rw [Real.rpow_add hc0, Real.rpow_one]; ring
      _ ≤ (2 * K * Real.log N) * (2 * K * Real.log N) / N := by
          gcongr
          exact (hcle N).trans h1
      _ = (2 * K) ^ 2 * (Real.log N ^ 2 / N) := by ring

/-! ### The second-order term from the bulk -/

/-- **The window aliasing is the bulk limit.** If `s^β E₁(s) → J`, then along `c → ∞`,
`c^{β+2}/N → 0`: `(c^{β+1}/∫φ²) 𝒜_N → β J ∫ e^{−βy} h(y)² dy`. -/
theorem tendsto_rpow_mul_horizonAlias_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ (β + 2) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N ^ (β + 1) / (∫ u, φ u ^ 2) * horizonAlias φ h (c N) N) atTop
      (𝓝 (J * (β * ∫ y, Real.exp (-(β * y)) * h y ^ 2))) := by
  have hg2 : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg2 hgs
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hgs) hg2 (by norm_num)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  set M := ∫ u, φ u ^ 2 with hM
  set s₀ := Real.exp (-A) with hs₀
  have hs₀0 : 0 < s₀ := Real.exp_pos _
  set Ba := Cφ * (2 * Real.pi * s₀) ^ (-p) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (-p) with hBa
  set La := 4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) * (2 * Real.pi * s₀) ^ (-p / 2) *
    (∑' k : ℕ, ((k : ℝ) + 1) ^ (1 - p / 2)) with hLa
  have hBas : ∀ s, s₀ ≤ s → aliasDensity φ s ≤ Ba := fun s hs =>
    aliasDensity_le hφ hφsupp (by linarith) hdecay hCφ hs₀0 hs
  have hLas : ∀ s s', s₀ ≤ s → s₀ ≤ s' → |aliasDensity φ s - aliasDensity φ s'| ≤ La * |s - s'| :=
    fun s s' hs hs' => abs_aliasDensity_sub_le hφ hφsupp hp hCφ hdecay hs₀0 hs hs'
  have hBa0 : 0 ≤ Ba := (aliasDensity_nonneg (φ := φ) s₀).trans (hBas s₀ le_rfl)
  have hLa0 : 0 ≤ La := by
    have := hLas s₀ (s₀ + 1) le_rfl (by linarith)
    rw [sub_add_cancel_left, abs_neg, abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  set D := 2 / M * ((Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * La) with hD
  have hEc : ContinuousOn (completedShellEnergy φ) (Set.Ioi 0) := fun s hs =>
    (hasDerivAt_completedShellEnergy hφ hφsupp hφ2 hs).continuousAt.continuousWithinAt
  set ℓ := Real.exp (-A - 1) with hℓ
  have hℓ0 : 0 < ℓ := Real.exp_pos _
  have hℓ1 : ℓ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hW := tendsto_window_bulk hbulk hEc (continuous_logProfileDeriv hg2 hgs) hℓ0 hℓ1 hcinf
  rw [integral_logProfileDeriv_mul_rpow hh hA hsupp β] at hW
  -- the discretization error
  have herr : Tendsto (fun N : ℕ => c N ^ (β + 1) / M * horizonAlias φ h (c N) N -
      c N ^ β * ∫ x in ℓ..1, logProfileDeriv (fun y => h y ^ 2) x *
        completedShellEnergy φ (c N * x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((hcN.const_mul D).trans (by rw [mul_zero]))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hlip := abs_windowAlias_sub_le hh hsupp hA hBg hLg hBas hLas (hc1 N)
    have hK0 : 0 ≤ (Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * (La * c N) := by positivity
    have hR := abs_riemann_sub_le_of_lipschitz hK0 hlip hN
    have hI := integral_windowAlias_eq hφ hφsupp hφ2 hh hsupp hA hc0
    rw [hI] at hR
    have hal := horizonAlias_eq_riemann hsupp φ (c N) hN (A := A)
    have hcβ : c N ^ (β + 1) = c N ^ β * c N := by rw [Real.rpow_add hc0, Real.rpow_one]
    have hcβ2 : c N ^ (β + 2) = c N ^ (β + 1) * c N := by
      rw [show β + 2 = (β + 1) + 1 by ring, Real.rpow_add hc0, Real.rpow_one]
    have hpos : 0 < c N ^ (β + 1) := Real.rpow_pos_of_pos hc0 _
    set R := (N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, windowAlias φ h A (c N) (r / N) with hRdef
    set W := ∫ x in ℓ..1, logProfileDeriv (fun y => h y ^ 2) x * completedShellEnergy φ (c N * x)
      with hWdef
    have heq : c N ^ (β + 1) / M * horizonAlias φ h (c N) N - c N ^ β * W =
        2 * c N ^ (β + 1) / M * (R - M / (2 * c N) * W) := by
      rw [hal, hcβ]; field_simp
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    calc 2 * c N ^ (β + 1) / M * |R - M / (2 * c N) * W| ≤
          2 * c N ^ (β + 1) / M * (((Lg : ℝ) * Real.exp (2 * A) * Ba + Bg * (La * c N)) / N) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ 2 * c N ^ (β + 1) / M * (((Lg : ℝ) * Real.exp (2 * A) * Ba * c N + Bg * (La * c N)) / N) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hN0.le) (by positivity)
          have := le_mul_of_one_le_right (by positivity : 0 ≤ (Lg : ℝ) * Real.exp (2 * A) * Ba) (hc1 N)
          linarith
      _ = D * (c N ^ (β + 2) / N) := by rw [hD, hcβ2]; field_simp
  have := herr.add hW
  rw [zero_add] at this
  exact this.congr fun N => by ring

/-- **The bulk determines the second-order term.** For a `C²` profile on `[0, 1]` with
`|φ̂(u)|² ≤ C_φ (1 + |u|)^{−p}`, `p > 4`, whose bulk energy has the rescaled limit
`s^β E₁(s) → J`, and a `C²` window profile `h` on `[−A, 0]`: along `c^{β+1}/log N → K > 0`,
`c⁻¹ ⟨W x, x⟩ → κ Q(H) + (β J/K) ∫ e^{−(β+1)y} H(y)² dy`, `H = e^{y/2} h`. -/
theorem horizon_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) +
        β * J / K * ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, hcN⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  rw [show β + 1 + 1 = β + 2 by ring] at hcN
  have hsharp := horizon_layer_sharp hφ hφsupp hφ2 (by linarith : (1 : ℝ) < p) hCφ hdecay hh hA
    hsupp hc1 hcinf hclog
  set M := ∫ u, φ u ^ 2 with hM
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  have halias := tendsto_rpow_mul_horizonAlias_of_regularBulk hφ hφsupp hφ2 hp hCφ hdecay hbulk
    hh hA hsupp hc1 hcinf hcN
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (β + 1)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  have hterm : Tendsto (fun N : ℕ => Real.log N / M * horizonAlias φ h (c N) N) atTop
      (𝓝 (K⁻¹ * (J * (β * I)))) := by
    refine (hinv.mul halias).congr fun N => ?_
    have hc0 : 0 < c N ^ (β + 1) := Real.rpow_pos_of_pos (by linarith [hc1 N]) _
    have hM0 : M ≠ 0 := hφ2.ne'
    rw [← hM]
    field_simp
  have := (hsharp.add (tendsto_const_nhds (x := (∫ u, φ u) ^ 2 / M *
    weilQuad (halfWeight h)))).add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : (∫ u, φ u) ^ 2 / M * weilQuad (halfWeight h) + K⁻¹ * (J * (β * I)) =
      (∫ u, φ u) ^ 2 / M * weilQuad (halfWeight h) + β * J / K * I := by
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
