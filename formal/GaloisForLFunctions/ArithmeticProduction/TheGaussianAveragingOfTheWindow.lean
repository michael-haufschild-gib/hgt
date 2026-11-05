import GaloisForLFunctions.ArithmeticProduction.TheFloorsOfTheMollifiedSecondMoment

/-!
# Averaging the Gaussian window over a long interval

The interpolation inequality lives at one height `t₀` and one Gaussian width `w`.  This module turns it into a statement about a sharp interval.

* `norm_sq_lineFun_mollifiedWindow`: on `Re s = ½ + x` the window function has square `P_x(t) e^{x²/w²} H(t, t₀)`, where
  `P_x(t) = |((s−1)/(s+1)) ζ(s) M(s)|²` and `H(t, t₀) = e^{−(t−t₀)²/w²}`.
* `integrated_gauss_inequality`: integrating a pointwise inequality in `t₀` over `[A₁, B₁]` and using Fubini replaces `H` by
  `Ψ(t) = ∫_{A₁}^{B₁} H(t, t₀) dt₀`, with `Ψ ≤ w√π` everywhere and `Ψ` close to `w√π` inside the interval
  (`gaussKernel_mass_le`, `gaussKernel_mass_ge`).
* `window_inequality`: the interpolation inequality for the window function, with its remainder made explicit in `N`, `t₀`, `w`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- The Gaussian kernel `H(t, t₀) = e^{−(t−t₀)²/w²}`. -/
def gaussKernel (w t t₀ : ℝ) : ℝ := Real.exp (-((t - t₀) ^ 2 / w ^ 2))

theorem gaussKernel_pos (w t t₀ : ℝ) : 0 < gaussKernel w t t₀ := Real.exp_pos _

theorem continuous_gaussKernel_uncurry (w : ℝ) :
    Continuous fun p : ℝ × ℝ => gaussKernel w p.1 p.2 := by
  unfold gaussKernel
  fun_prop

private theorem half_width_sq {w : ℝ} : 2 * (w / √2) ^ 2 = w ^ 2 := by
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, hsq2]
  ring

private theorem half_width_mass {w : ℝ} : w / √2 * √(2 * Real.pi) = w * √Real.pi := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : √(2 : ℝ) ≠ 0 := by positivity
  field_simp

theorem integrable_gaussKernel_right {w : ℝ} (hw : 0 < w) (t : ℝ) :
    Integrable fun t₀ => gaussKernel w t t₀ := by
  have hw' : 0 < w / √2 := by positivity
  refine (integrable_gauss t hw').congr (Filter.Eventually.of_forall fun t₀ => ?_)
  simp only [gaussKernel]
  rw [half_width_sq]
  congr 2
  ring

theorem integrable_gaussKernel_left {w : ℝ} (hw : 0 < w) (t₀ : ℝ) :
    Integrable fun t => gaussKernel w t t₀ := by
  have hw' : 0 < w / √2 := by positivity
  refine (integrable_gauss t₀ hw').congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [gaussKernel]
  rw [half_width_sq]

/-- The total mass of the Gaussian kernel. -/
theorem integral_gaussKernel_right {w : ℝ} (hw : 0 < w) (t : ℝ) :
    ∫ t₀, gaussKernel w t t₀ = w * √Real.pi := by
  have hw' : 0 < w / √2 := by positivity
  have h := integral_gauss t hw'
  rw [half_width_mass] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t₀ => ?_)
  simp only [gaussKernel]
  rw [half_width_sq]
  congr 2
  ring

/-- `Ψ(t) ≤ w√π`. -/
theorem gaussKernel_mass_le {w : ℝ} (hw : 0 < w) (t : ℝ) {A B : ℝ} (hAB : A ≤ B) :
    ∫ t₀ in A..B, gaussKernel w t t₀ ≤ w * √Real.pi := by
  rw [intervalIntegral.integral_of_le hAB, ← integral_gaussKernel_right hw t]
  exact setIntegral_le_integral (integrable_gaussKernel_right hw t)
    (Filter.Eventually.of_forall fun t₀ => (gaussKernel_pos w t t₀).le)

/-- `Ψ(t) ≥ w√π − e^{−R²/(2w²)} w√(2π)` when `t` is at distance `R` from the ends. -/
theorem gaussKernel_mass_ge {w : ℝ} (hw : 0 < w) {t A B R : ℝ} (hAB : A ≤ B) (hR : 0 ≤ R)
    (hA : A + R ≤ t) (hB : t ≤ B - R) :
    w * √Real.pi - Real.exp (-(R ^ 2 / (2 * w ^ 2))) * (w * √(2 * Real.pi)) ≤
      ∫ t₀ in A..B, gaussKernel w t t₀ := by
  have hint := integrable_gaussKernel_right hw t
  have hsplit := integral_add_compl (measurableSet_Ioc (a := A) (b := B)) hint
  rw [integral_gaussKernel_right hw t] at hsplit
  rw [intervalIntegral.integral_of_le hAB]
  have hcompl : ∫ t₀ in (Ioc A B)ᶜ, gaussKernel w t t₀ ≤
      Real.exp (-(R ^ 2 / (2 * w ^ 2))) * (w * √(2 * Real.pi)) := by
    have hg : Integrable fun t₀ : ℝ =>
        Real.exp (-(R ^ 2 / (2 * w ^ 2))) * Real.exp (-((t₀ - t) ^ 2 / (2 * w ^ 2))) :=
      (integrable_gauss t hw).const_mul _
    have hle : ∫ t₀ in (Ioc A B)ᶜ, gaussKernel w t t₀ ≤
        ∫ t₀ in (Ioc A B)ᶜ, Real.exp (-(R ^ 2 / (2 * w ^ 2))) *
          Real.exp (-((t₀ - t) ^ 2 / (2 * w ^ 2))) := by
      refine setIntegral_mono_on hint.integrableOn hg.integrableOn
        measurableSet_Ioc.compl fun t₀ ht₀ => ?_
      have hdist : R ^ 2 ≤ (t₀ - t) ^ 2 := by
        have hnot : ¬ (A < t₀ ∧ t₀ ≤ B) := ht₀
        by_cases h1 : t₀ ≤ A
        · have h2 : R ≤ t - t₀ := by linarith
          have h3 := pow_le_pow_left₀ hR h2 2
          have h4 : (t - t₀) ^ 2 = (t₀ - t) ^ 2 := by ring
          rwa [h4] at h3
        · have h2 : B < t₀ := by
            by_contra h3
            exact hnot ⟨not_le.mp h1, not_lt.mp h3⟩
          have h3 : R ≤ t₀ - t := by linarith
          exact pow_le_pow_left₀ hR h3 2
      simp only [gaussKernel]
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hw2 : 0 < w ^ 2 := by positivity
      have h5 : (t - t₀) ^ 2 / w ^ 2 = (t₀ - t) ^ 2 / (2 * w ^ 2) + (t₀ - t) ^ 2 / (2 * w ^ 2) := by
        field_simp
        ring
      have h6 : R ^ 2 / (2 * w ^ 2) ≤ (t₀ - t) ^ 2 / (2 * w ^ 2) :=
        div_le_div_of_nonneg_right hdist (by positivity)
      rw [h5]
      linarith
    refine hle.trans ?_
    have hle2 := setIntegral_le_integral (s := (Ioc A B)ᶜ) hg
      (Filter.Eventually.of_forall fun t₀ => by
        show 0 ≤ _
        positivity)
    have hRHS : ∫ t₀ : ℝ, Real.exp (-(R ^ 2 / (2 * w ^ 2))) *
        Real.exp (-((t₀ - t) ^ 2 / (2 * w ^ 2))) =
        Real.exp (-(R ^ 2 / (2 * w ^ 2))) * (w * √(2 * Real.pi)) := by
      rw [integral_const_mul, integral_gauss t hw]
    rwa [hRHS] at hle2
  linarith

/-- **Integrating a pointwise inequality against the Gaussian kernel.** -/
theorem integrated_gauss_inequality {w A₁ B₁ c₁ c₂ c₃ τ ψ T₁ T₂ T₃ T₄ : ℝ} {P Q : ℝ → ℝ} (hw : 0 < w)
    (hAB : A₁ ≤ B₁) (hT12 : T₁ ≤ T₂) (hT34 : T₃ ≤ T₄) (hP : Continuous P) (hQ : Continuous Q)
    (hP0 : ∀ t, 0 ≤ P t) (hQ0 : ∀ t, 0 ≤ Q t) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (h : ∀ t₀ ∈ Icc A₁ B₁, c₁ + c₂ * (∫ t in T₁..T₂, P t * gaussKernel w t t₀) ≤
      c₃ * (∫ t in T₃..T₄, Q t * gaussKernel w t t₀) + τ)
    (hψ : ∀ t ∈ Icc T₁ T₂, ψ ≤ ∫ t₀ in A₁..B₁, gaussKernel w t t₀) :
    c₁ * (B₁ - A₁) + c₂ * ψ * (∫ t in T₁..T₂, P t) ≤
      c₃ * (w * √Real.pi) * (∫ t in T₃..T₄, Q t) + τ * (B₁ - A₁) := by
  have hcontP : Continuous fun p : ℝ × ℝ => P p.2 * gaussKernel w p.2 p.1 :=
    (hP.comp continuous_snd).mul ((continuous_gaussKernel_uncurry w).comp
      (continuous_snd.prodMk continuous_fst))
  have hcontQ : Continuous fun p : ℝ × ℝ => Q p.2 * gaussKernel w p.2 p.1 :=
    (hQ.comp continuous_snd).mul ((continuous_gaussKernel_uncurry w).comp
      (continuous_snd.prodMk continuous_fst))
  have hX : Continuous fun t₀ => ∫ t in T₁..T₂, P t * gaussKernel w t t₀ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun t₀ t => P t * gaussKernel w t t₀) hcontP T₁ T₂
  have hY : Continuous fun t₀ => ∫ t in T₃..T₄, Q t * gaussKernel w t t₀ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun t₀ t => Q t * gaussKernel w t t₀) hcontQ T₃ T₄
  have hmono : ∫ t₀ in A₁..B₁, (c₁ + c₂ * ∫ t in T₁..T₂, P t * gaussKernel w t t₀) ≤
      ∫ t₀ in A₁..B₁, (c₃ * (∫ t in T₃..T₄, Q t * gaussKernel w t t₀) + τ) :=
    intervalIntegral.integral_mono_on hAB
      ((continuous_const.add (continuous_const.mul hX)).intervalIntegrable _ _)
      (((continuous_const.mul hY).add continuous_const).intervalIntegrable _ _) h
  have hswap : ∀ {R : ℝ → ℝ} {a b : ℝ}, Continuous R →
      ∫ t₀ in A₁..B₁, ∫ t in a..b, R t * gaussKernel w t t₀ =
        ∫ t in a..b, R t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀ := by
    intro R a b hR
    have hcont : Continuous (Function.uncurry fun t₀ t => R t * gaussKernel w t t₀) :=
      (hR.comp continuous_snd).mul ((continuous_gaussKernel_uncurry w).comp
        (continuous_snd.prodMk continuous_fst))
    have hI : IntegrableOn (Function.uncurry fun t₀ t => R t * gaussKernel w t t₀)
        (Set.uIoc A₁ B₁ ×ˢ Set.uIoc a b) :=
      (hcont.continuousOn.integrableOn_compact
        ((isCompact_uIcc (a := A₁) (b := B₁)).prod (isCompact_uIcc (a := a) (b := b)))).mono_set
        (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    rw [intervalIntegral_intervalIntegral_swap hI]
    refine intervalIntegral.integral_congr fun t _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  have hPsiCont : Continuous fun t => ∫ t₀ in A₁..B₁, gaussKernel w t t₀ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun t t₀ => gaussKernel w t t₀) (continuous_gaussKernel_uncurry w) A₁ B₁
  -- left side
  have hL : ∫ t₀ in A₁..B₁, (c₁ + c₂ * ∫ t in T₁..T₂, P t * gaussKernel w t t₀) =
      c₁ * (B₁ - A₁) + c₂ * ∫ t in T₁..T₂, P t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀ := by
    have hcX : Continuous fun t₀ => c₂ * ∫ t in T₁..T₂, P t * gaussKernel w t t₀ :=
      continuous_const.mul hX
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      (hcX.intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, hswap hP, smul_eq_mul]
    ring
  have hR : ∫ t₀ in A₁..B₁, (c₃ * (∫ t in T₃..T₄, Q t * gaussKernel w t t₀) + τ) =
      c₃ * (∫ t in T₃..T₄, Q t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀) + τ * (B₁ - A₁) := by
    have hcY : Continuous fun t₀ => c₃ * ∫ t in T₃..T₄, Q t * gaussKernel w t t₀ :=
      continuous_const.mul hY
    rw [intervalIntegral.integral_add (hcY.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, hswap hQ, smul_eq_mul]
    ring
  rw [hL, hR] at hmono
  have hlow : ψ * (∫ t in T₁..T₂, P t) ≤ ∫ t in T₁..T₂, P t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT12
      ((continuous_const.mul hP).intervalIntegrable _ _)
      ((hP.mul hPsiCont).intervalIntegrable _ _) fun t ht => ?_
    have := mul_le_mul_of_nonneg_left (hψ t ht) (hP0 t)
    linarith
  have hup : (∫ t in T₃..T₄, Q t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀) ≤
      (w * √Real.pi) * ∫ t in T₃..T₄, Q t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT34
      ((hQ.mul hPsiCont).intervalIntegrable _ _)
      ((continuous_const.mul hQ).intervalIntegrable _ _) fun t _ => ?_
    have := mul_le_mul_of_nonneg_left (gaussKernel_mass_le hw t hAB) (hQ0 t)
    linarith
  have h1 := mul_le_mul_of_nonneg_left hlow hc₂
  have h2 := mul_le_mul_of_nonneg_left hup hc₃
  calc c₁ * (B₁ - A₁) + c₂ * ψ * (∫ t in T₁..T₂, P t)
      = c₁ * (B₁ - A₁) + c₂ * (ψ * ∫ t in T₁..T₂, P t) := by ring
    _ ≤ c₁ * (B₁ - A₁) + c₂ * ∫ t in T₁..T₂, P t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀ := by
        linarith
    _ ≤ c₃ * (∫ t in T₃..T₄, Q t * ∫ t₀ in A₁..B₁, gaussKernel w t t₀) + τ * (B₁ - A₁) := hmono
    _ ≤ c₃ * ((w * √Real.pi) * ∫ t in T₃..T₄, Q t) + τ * (B₁ - A₁) := by linarith
    _ = _ := by ring

/-- The square of the body on a vertical line. -/
def linePower (b : ℕ → ℂ) (N : ℕ) (x t : ℝ) : ℝ :=
  ‖windowBody b N (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2

theorem continuous_linePower (b : ℕ → ℂ) (N : ℕ) {x : ℝ} (hx : -3 / 2 < x) :
    Continuous (linePower b N x) := by
  unfold linePower
  refine (continuous_iff_continuousAt.mpr fun t => ?_).norm.pow 2
  have hre : -1 < (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I).re := by
    simp
    linarith
  exact ContinuousAt.comp (f := fun t : ℝ => ((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I)
    (g := windowBody b N) (differentiableAt_windowBody b N hre).continuousAt (by fun_prop)

theorem linePower_nonneg (b : ℕ → ℂ) (N : ℕ) (x t : ℝ) : 0 ≤ linePower b N x t := by
  unfold linePower
  positivity

/-- **The window function on a line.** -/
theorem norm_sq_lineFun_mollifiedWindow (t₀ : ℝ) {w : ℝ} (hw : 0 < w) (b : ℕ → ℂ) (N : ℕ) (x t : ℝ) :
    ‖lineFun (mollifiedWindow t₀ w b N) x t‖ ^ 2 =
      linePower b N x t * Real.exp (x ^ 2 / w ^ 2) * gaussKernel w t t₀ := by
  unfold lineFun mollifiedWindow linePower gaussKernel
  rw [norm_mul, mul_pow, norm_gaussWindow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, mul_one, sub_zero, Complex.add_im, Complex.mul_im,
    zero_add, add_zero]
  push_cast
  field_simp
  ring

/-- **The interpolation inequality for the window function.** -/
theorem exists_window_inequality :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (t₀ : ℝ) {w a L B : ℝ} (_ : 0 < w) (_ : 0 < a) (_ : a ≤ 1 / 4) (_ : 0 ≤ L)
      (_ : 0 ≤ B) {b : ℕ → ℂ} {N : ℕ} (_ : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1),
      Real.exp (L * a) * (∫ t, ‖lineFun (mollifiedWindow t₀ w b N) a t‖ ^ 2) +
          Real.exp (-(L * a)) * (∫ t, ‖lineFun (mollifiedWindow t₀ w b N) (-a) t‖ ^ 2) ≤
        2 * Real.cosh (a * (L + 2 * B)) * (∫ t, ‖lineFun (mollifiedWindow t₀ w b N) 0 t‖ ^ 2) +
          ((4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * √(2 * Real.pi))) ^ 2 * Real.exp (L * a) *
                Real.exp (-(2 * B * (3 / 2 - a))) / (2 * Real.pi * (3 / 2 - a)) +
            (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
                (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * √(2 * Real.pi)))) ^ 2 *
                Real.exp (-(L * a)) * Real.exp (-(2 * (L + B) * (1 - a))) /
              (2 * Real.pi * (1 - a))) := by
  obtain ⟨A, hA, hleft⟩ := exists_integral_norm_mollifiedWindow_left_le
  refine ⟨A, hA, ?_⟩
  intro t₀ w a L B hw ha ha1 hL hB b N hb
  obtain ⟨C, hC⟩ := exists_stripDecay_mollifiedWindow t₀ hw hb
  have hmain := cosh_interpolation hC (by norm_num) (by norm_num) ha (by linarith) (by linarith) hL hB
  have hπ := Real.pi_pos
  have hc₂ : 0 < 3 / 2 - a := by linarith
  have hc₁ : 0 < 1 - a := by linarith
  have hneg : (- -1 - a : ℝ) = 1 - a := by ring
  rw [hneg] at hmain
  refine hmain.trans (add_le_add le_rfl (add_le_add ?_ ?_))
  · have h1 := integral_norm_mollifiedWindow_right_le t₀ hw hb
    have h2 : 0 ≤ ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) (3 / 2) t‖ :=
      integral_nonneg fun t => norm_nonneg _
    have h3 := pow_le_pow_left₀ h2 h1 2
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
      (Real.exp_pos _).le
  · have h1 := hleft t₀ hw hb
    have h2 : 0 ≤ ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) (-1) t‖ :=
      integral_nonneg fun t => norm_nonneg _
    have h3 := pow_le_pow_left₀ h2 h1 2
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
      (Real.exp_pos _).le

end GaloisForLFunctions.ArithmeticProduction
