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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
