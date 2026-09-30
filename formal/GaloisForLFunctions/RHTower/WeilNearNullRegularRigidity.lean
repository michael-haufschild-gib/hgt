import GaloisForLFunctions.RHTower.WeilRegularDeviationRigidity
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalBoundary
import GaloisForLFunctions.RHTower.WeilFullConeCompactness

/-!
# Near-null regular rigidity: no regular witness of radical evaporation

Let `u : ℕ → ℝ` be a bounded sequence on `n ≥ 2` and `K = Φ⋆Φ` Riemann's autocorrelation, with
`𝓕K = Ξ²`. The **null potential** is `ψ_u(y) = Σ_n u(n)(K(y + log n) + K(y − log n))`. Its
positive-definiteness (up to sign) is the statement `Ξ(t)² · Σ u(n) cos(t log n) ≤ 0` as a
measure. Near-null Weil positivity forces this for the normalized deviation
`u = (lam − Λ)/√n` of every full-cone Weil-positive `lam`, and it involves `u` alone.

**Theorem** (`eq_zero_of_positiveDefinite_neg_nullPotential`). Let `w = u√n` be a regular
deviation (`RegularDeviation`): its Dirichlet series continues holomorphically across the strip
`½ ≤ Re s ≤ 7/4`, with linear growth and real symmetry. If `−ψ_u` is positive definite, then
`u = 0`. By symmetry the same holds for `+ψ_u` (`eq_zero_of_positiveDefinite_nullPotential`).

So a nonzero bounded `u` with `Ξ² · Σ u(n) cos(t log n)` of one sign must have a Dirichlet series
that is singular on the critical line.

**Proof.**
- **Sign.** By Bochner, `−ψ_u = charFun σ` for a finite positive measure `σ`. The critical-line
  representation with the test `Ξ²` gives `ψ_u(t) = ∫ e^{2πiξt} Ξ(ξ)² · 2 Re E(½ + 2πiξ) dξ`.
  Uniqueness of characteristic functions makes `Ξ²·Re E ≤ 0`, and the real zeros of `Ξ` are
  isolated. Hence `Re E ≤ 0` on the critical line.
- **Annihilation.** The autocorrelation `k` of a bump supported in `[−¼, ¼]` vanishes at every
  `±log n`, `n ≥ 2`. So `∫ |ĝ|² Re E(½ + 2πiξ) dξ = 0`, which forces `Re E ≡ 0`.
- **Vanishing.** Narrow bumps centred at `log m` then read off `u(m) = 0`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23 GaloisForLFunctions.RHTower RHTower.WeilOneSided

namespace RHTower.WeilRegular

noncomputable section

/-! ## Decay of `Ξ` on the strip `|Im| ≤ 5/4` -/

theorem xi_half_add_mul_I (t a : ℝ) :
    (1 / 2 : ℂ) + ((t : ℂ) + (a : ℂ) * I) * I = ((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I := by
  apply Complex.ext
  · simp; ring
  · simp

theorem exists_norm_XiC_wide_le :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ t a : ℝ, |a| ≤ 5 / 4 →
      ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 4)) := by
  obtain ⟨C₁, N, hC₁, hdec⟩ := RHTower.SelbergThetaHorizontalBoundary.xi_strip_decay
  set K : Set ℂ := {z | |z.re| ≤ 2} ∩ {z | |z.im| ≤ 5 / 4} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 + 5 / 4)).subset fun z hz => ?_
      obtain ⟨h1, h2⟩ := hz
      simp only [mem_setOf_eq] at h1 h2
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn RHTower.XiC_differentiable.continuous.continuousOn
  refine ⟨C₁ + max M 0 * Real.exp (π / 2), N, by positivity, fun t a ha => ?_⟩
  have hpow : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  have hexp0 : 0 < Real.exp (-(π * |t| / 4)) := Real.exp_pos _
  by_cases ht : |t| ≤ 2
  · have hz : ((t : ℂ) + (a : ℂ) * I) ∈ K := by
      refine ⟨?_, ?_⟩ <;> simp only [mem_setOf_eq] <;> simp [ht, ha]
    have hb := hM _ hz
    have he : 1 ≤ Real.exp (π / 2) * Real.exp (-(π * |t| / 4)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos])
    calc ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ max M 0 := hb.trans (le_max_left _ _)
      _ ≤ max M 0 * (Real.exp (π / 2) * Real.exp (-(π * |t| / 4))) :=
          le_mul_of_one_le_right (le_max_right _ _) he
      _ ≤ max M 0 * Real.exp (π / 2) * (1 + |t|) ^ N * Real.exp (-(π * |t| / 4)) := by
          have h0 : 0 ≤ max M 0 * Real.exp (π / 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg h0 hexp0.le)]
      _ ≤ (C₁ + max M 0 * Real.exp (π / 2)) * (1 + |t|) ^ N * Real.exp (-(π * |t| / 4)) := by
          gcongr; linarith
  · rw [not_le] at ht
    have hmain : ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ C₁ * |t| ^ N * Real.exp (-(π * |t| / 4)) := by
      rcases le_total a 0 with hale | hage
      · have h := hdec (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) (by simp; linarith)
          (by simp; linarith [neg_abs_le a, abs_le.mp ha]) (by simp; linarith)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h
        unfold XiC; rwa [xi_half_add_mul_I]
      · have h := hdec (((1 / 2 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) (by simp; linarith)
          (by simp; linarith [le_abs_self a, abs_le.mp ha]) (by simp; linarith)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, abs_neg] at h
        rw [← RHTower.XiC_even]
        unfold XiC
        rw [show (1 / 2 : ℂ) + -((t : ℂ) + (a : ℂ) * I) * I =
          ((1 / 2 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I by apply Complex.ext <;> simp]
        exact h
    calc ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ C₁ * |t| ^ N * Real.exp (-(π * |t| / 4)) := hmain
      _ ≤ C₁ * (1 + |t|) ^ N * Real.exp (-(π * |t| / 4)) := by
          gcongr; linarith
      _ ≤ (C₁ + max M 0 * Real.exp (π / 2)) * (1 + |t|) ^ N * Real.exp (-(π * |t| / 4)) := by
          gcongr; have : 0 ≤ max M 0 * Real.exp (π / 2) := by positivity
          linarith

/-! ## The test `Ξ²` -/

/-- The frequency weight `XiC(2πz)²`, the transform of Riemann's autocorrelation. -/
def xiSq (z : ℂ) : ℂ := XiC (2 * π * z) ^ 2

theorem differentiable_xiSq : Differentiable ℂ xiSq := by
  unfold xiSq
  exact ((RHTower.XiC_differentiable).comp (by fun_prop)).pow 2

theorem one_add_pow_mul_exp_le (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    (1 + v) ^ m * Real.exp (-(π / 2 * v)) ≤ m.factorial * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (1 + v) (by linarith) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  rw [div_le_iff₀ hf] at h
  have he : Real.exp (1 + v) * Real.exp (-(π / 2 * v)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := Real.pi_gt_three; nlinarith
  calc (1 + v) ^ m * Real.exp (-(π / 2 * v))
      ≤ Real.exp (1 + v) * m.factorial * Real.exp (-(π / 2 * v)) := by gcongr
    _ = m.factorial * (Real.exp (1 + v) * Real.exp (-(π / 2 * v))) := by ring
    _ ≤ m.factorial * Real.exp 1 := by gcongr

theorem exists_norm_xiSq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖xiSq z‖ ≤ C * ((1 + |z.re|) ^ 3)⁻¹ := by
  obtain ⟨C, N, hC0, hC⟩ := exists_norm_XiC_wide_le
  refine ⟨C ^ 2 * ((2 * N + 3).factorial * Real.exp 1), by positivity, fun z hz => ?_⟩
  have hz' : 2 * π * z = ((2 * π * z.re : ℝ) : ℂ) + ((2 * π * z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have ha : |2 * π * z.im| ≤ 5 / 4 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have := two_pi_mul_shiftHeight
    nlinarith [Real.pi_pos]
  have h := hC (2 * π * z.re) (2 * π * z.im) ha
  set v : ℝ := |2 * π * z.re| with hv
  have hv0 : 0 ≤ v := abs_nonneg _
  have hxv : |z.re| ≤ v := by
    rw [hv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have := Real.pi_gt_three; nlinarith [abs_nonneg z.re]
  have hsq : ‖xiSq z‖ ≤ C ^ 2 * ((1 + v) ^ (2 * N) * Real.exp (-(π / 2 * v))) := by
    unfold xiSq
    rw [norm_pow, hz']
    calc ‖XiC (((2 * π * z.re : ℝ) : ℂ) + ((2 * π * z.im : ℝ) : ℂ) * I)‖ ^ 2
        ≤ (C * (1 + v) ^ N * Real.exp (-(π * v / 4))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ 2 * ((1 + v) ^ (2 * N) * Real.exp (-(π / 2 * v))) := by
          have he : Real.exp (-(π * v / 4)) ^ 2 = Real.exp (-(π / 2 * v)) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
          rw [mul_pow, mul_pow, ← pow_mul, he]; ring
  have hkey := one_add_pow_mul_exp_le (2 * N + 3) hv0
  have hp : 0 < (1 + |z.re|) ^ 3 := by positivity
  rw [le_mul_inv_iff₀ hp]
  calc ‖xiSq z‖ * (1 + |z.re|) ^ 3
      ≤ C ^ 2 * ((1 + v) ^ (2 * N) * Real.exp (-(π / 2 * v))) * (1 + v) ^ 3 := by
        gcongr
    _ = C ^ 2 * ((1 + v) ^ (2 * N + 3) * Real.exp (-(π / 2 * v))) := by ring
    _ ≤ C ^ 2 * ((2 * N + 3).factorial * Real.exp 1) := by gcongr

theorem xiSq_ofReal (ξ : ℝ) : xiSq ξ = RHTower.WeilExcess.riemannXi ξ ^ 2 := by
  rw [xiSq, RHTower.WeilExcess.riemannXi_eq_XiC]

theorem xiSq_ofReal_eq (ξ : ℝ) :
    xiSq ξ = ((RHTower.WeilExcess.riemannXiReal ξ ^ 2 : ℝ) : ℂ) := by
  rw [xiSq_ofReal, RHTower.WeilExcess.riemannXi_eq_ofReal]; push_cast; ring

theorem xiSq_zero_ne : xiSq 0 ≠ 0 := by
  have h := RHTower.WeilExcess.riemannXiReal_zero_ne
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, xiSq_ofReal_eq]
  exact_mod_cast pow_ne_zero 2 h

theorem integrable_riemannAutocorr_ofReal :
    Integrable fun y => ((RHTower.riemannAutocorr y : ℝ) : ℂ) := by
  have : Integrable RHTower.riemannAutocorr := by
    obtain ⟨C₁, -, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
    refine Integrable.mono' ((integrable_exp_neg_abs.comp_mul_left' (two_ne_zero)).const_mul C₁)
      RHTower.WeilExcess.continuous_riemannAutocorr.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (RHTower.WeilExcess.riemannAutocorr_nonneg y)]
    refine (hC₁ y).trans (le_of_eq ?_)
    simp only [abs_mul, abs_two, mul_comm]
  exact this.ofReal

/-- **Fourier inversion for `K`:** `K(u) = ∫ XiC(2πξ)² e^{2πiξu} dξ`. -/
theorem riemannAutocorr_eq_integral (u : ℝ) :
    ((RHTower.riemannAutocorr u : ℝ) : ℂ) = ∫ ξ : ℝ, xiSq ξ * cexp (2 * π * I * ξ * u) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_xiSq_le
  have hK := integrable_riemannAutocorr_ofReal
  have hKc : Continuous fun y => ((RHTower.riemannAutocorr y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp RHTower.WeilExcess.continuous_riemannAutocorr
  have hFK : 𝓕 (fun y => ((RHTower.riemannAutocorr y : ℝ) : ℂ)) = fun ξ : ℝ => xiSq ξ := by
    funext ξ; rw [RHTower.WeilExcess.fourier_riemannAutocorr, xiSq_ofReal]
  have hFKi : Integrable (𝓕 (fun y => ((RHTower.riemannAutocorr y : ℝ) : ℂ))) := by
    rw [hFK]
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      ((differentiable_xiSq.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    have h := hC (ξ : ℂ) (by simp [shiftHeight_pos.le])
    simp only [Complex.ofReal_re] at h
    exact h.trans (mul_le_mul_of_nonneg_left (inv_one_add_abs_pow_three_le ξ) hC0)
  have hinv := hKc.fourierInv_fourier_eq hK hFKi
  have hu := congrFun hinv u
  rw [← hu, RHTower.WeilExcess.fourierInv_eq_integral, hFK]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [mul_comm]
  congr 1; congr 1; push_cast; ring

/-! ## Nonvanishing on the real line -/

/-- A nonzero entire function is nonzero at real points arbitrarily close to every real point. -/
theorem frequently_ne_zero_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₁ : ℂ}
    (h1 : F z₁ ≠ 0) (ξ₀ : ℝ) : ∃ᶠ ξ : ℝ in 𝓝 ξ₀, F ξ ≠ 0 := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  have hana : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  have htend : Tendsto (fun ξ : ℝ => (ξ : ℂ)) (𝓝[≠] ξ₀) (𝓝[≠] (ξ₀ : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto ξ₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ
      simp only [mem_compl_iff, mem_singleton_iff] at hξ ⊢
      exact fun h => hξ (Complex.ofReal_injective h)
  have hfreq : ∃ᶠ z in 𝓝[≠] (ξ₀ : ℂ), F z = 0 :=
    htend.frequently (hcon.filter_mono nhdsWithin_le_nhds).frequently
  have hev := (hana _ (mem_univ _)).frequently_zero_iff_eventually_zero.mp hfreq
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ _) hev
  exact h1 (hzero (mem_univ z₁))

/-- A continuous function that is `≤ 0` wherever an entire `F ≢ 0` is nonzero is `≤ 0`. -/
theorem nonpos_of_nonpos_off_zeros {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₁ : ℂ} (h1 : F z₁ ≠ 0)
    {q : ℝ → ℝ} (hq : Continuous q) (hq0 : ∀ ξ : ℝ, F ξ ≠ 0 → q ξ ≤ 0) (ξ₀ : ℝ) : q ξ₀ ≤ 0 :=
  (isClosed_le hq continuous_const).mem_of_frequently_of_tendsto
    ((frequently_ne_zero_of_differentiable hF h1 ξ₀).mono fun ξ hξ => hq0 ξ hξ) tendsto_id

/-- A continuous function that vanishes wherever an entire `F ≢ 0` is nonzero vanishes. -/
theorem eq_zero_of_eq_zero_off_zeros {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₁ : ℂ}
    (h1 : F z₁ ≠ 0) {q : ℝ → ℝ} (hq : Continuous q) (hq0 : ∀ ξ : ℝ, F ξ ≠ 0 → q ξ = 0)
    (ξ₀ : ℝ) : q ξ₀ = 0 :=
  (isClosed_eq hq continuous_const).mem_of_frequently_of_tendsto
    ((frequently_ne_zero_of_differentiable hF h1 ξ₀).mono fun ξ hξ => hq0 ξ hξ) tendsto_id

/-! ## The null potential -/

/-- The null potential `ψ_u(y) = Σ_n u(n)(K(y + log n) + K(y − log n))`. -/
def nullPotential (u : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, u n * (RHTower.riemannAutocorr (y + Real.log n) +
    RHTower.riemannAutocorr (y - Real.log n))

theorem continuous_nullPotential {u : ℕ → ℝ} (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ n, |u n| ≤ A) : Continuous (nullPotential u) := by
  have ha : ∀ n : ℕ, |u n| ≤ 2 * Real.log n + A := fun n => by
    have := Real.log_natCast_nonneg n; linarith [hu n]
  obtain ⟨C₁, -, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  rw [continuous_iff_continuousAt]
  intro y₀
  have hon : ContinuousOn (nullPotential u) (Metric.ball y₀ 1) := by
    refine continuousOn_tsum (fun n => ?_)
      ((RHTower.WeilExcess.summable_log_add_mul_inv_sq hA).mul_left
        (2 * C₁ * Real.exp (2 * (|y₀| + 1))))
      (fun n y hy => RHTower.WeilExcess.norm_potential_term_le
        RHTower.WeilExcess.riemannAutocorr_nonneg hC₁ ha hu0 hA ?_ n)
    · exact (continuous_const.mul ((RHTower.WeilExcess.continuous_riemannAutocorr.comp
        (continuous_id.add continuous_const)).add
        (RHTower.WeilExcess.continuous_riemannAutocorr.comp
          (continuous_id.sub continuous_const)))).continuousOn
    · rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y y₀
      linarith
  exact hon.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

/-! ## The line density and its sign -/

variable {w : ℕ → ℝ} {E : ℂ → ℂ}

/-- The critical-line density `Ξ(ξ)² · 2 Re E(½ + 2πiξ)`. -/
def lineDensity (E : ℂ → ℂ) (ξ : ℝ) : ℝ :=
  RHTower.WeilExcess.riemannXiReal ξ ^ 2 * (2 * (E (1 / 2 + 2 * π * I * ξ)).re)

theorem continuous_E_line (hR : RegularDeviation w E) :
    Continuous fun ξ : ℝ => E (1 / 2 + 2 * π * I * ξ) :=
  continuous_iff_continuousAt.mpr fun ξ =>
    (hR.differentiableAt _ (by simp) (by simp; norm_num)).continuousAt.comp
      (f := fun ξ : ℝ => (1 / 2 + 2 * π * I * ξ : ℂ)) (by fun_prop)

theorem continuous_lineDensity (hR : RegularDeviation w E) : Continuous (lineDensity E) := by
  unfold lineDensity
  exact (RHTower.WeilExcess.contDiff_riemannXiReal.continuous.pow 2).mul
    (continuous_const.mul (Complex.continuous_re.comp (continuous_E_line hR)))

theorem integrable_lineDensity (hR : RegularDeviation w E) : Integrable (lineDensity E) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_xiSq_le
  obtain ⟨CE, hCE, hEb⟩ := hR.growth
  refine (integrable_inv_one_add_sq.const_mul (C * (2 * CE) * (2 * π))).mono'
    (continuous_lineDensity hR).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have hX : RHTower.WeilExcess.riemannXiReal ξ ^ 2 ≤ C * ((1 + |ξ|) ^ 3)⁻¹ := by
    have h := hC (ξ : ℂ) (by simp [shiftHeight_pos.le])
    rw [xiSq_ofReal_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at h
    simpa using h
  have hE := hEb (1 / 2 + 2 * π * I * ξ) (by simp) (by simp; norm_num)
  have him : |(1 / 2 + 2 * π * I * ξ : ℂ).im| = 2 * π * |ξ| := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [him] at hE
  have hre : |(E (1 / 2 + 2 * π * I * ξ)).re| ≤ CE * (1 + 2 * π * |ξ|) :=
    (Complex.abs_re_le_norm _).trans hE
  have hk := inv_one_add_abs_pow_three_mul_le ξ
  unfold lineDensity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_two]
  calc RHTower.WeilExcess.riemannXiReal ξ ^ 2 * (2 * |(E (1 / 2 + 2 * π * I * ξ)).re|)
      ≤ C * ((1 + |ξ|) ^ 3)⁻¹ * (2 * (CE * (1 + 2 * π * |ξ|))) := by gcongr
    _ = C * (2 * CE) * (((1 + |ξ|) ^ 3)⁻¹ * (1 + 2 * π * |ξ|)) := by ring
    _ ≤ C * (2 * CE) * (2 * π * (1 + ξ ^ 2)⁻¹) := by gcongr
    _ = C * (2 * CE) * (2 * π) * (1 + ξ ^ 2)⁻¹ := by ring

/-- **The null potential on the critical line.**
`ψ_u(t) = ∫ e^{2πiξt} Ξ(ξ)² · 2 Re E(½ + 2πiξ) dξ` for `u = w/√n`. -/
theorem nullPotential_eq_integral (hR : RegularDeviation w E) (t : ℝ) :
    ((nullPotential (fun n => w n / Real.sqrt n) t : ℝ) : ℂ) =
      ∫ ξ : ℝ, cexp (2 * π * I * ξ * t) * (lineDensity E ξ : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_xiSq_le
  obtain ⟨CE, hCE, hEb⟩ := hR.growth
  have hRep := tsum_deviation_mul_pair_eq (G := xiSq)
    (g := fun u => ((RHTower.riemannAutocorr u : ℝ) : ℂ)) hR.zero hR.summable hR.series
    hR.differentiableAt hCE hEb hC0 (fun z _ => differentiable_xiSq z) hC
    riemannAutocorr_eq_integral t
  rw [nullPotential, Complex.ofReal_tsum]
  have hlhs : (∑' n : ℕ, ((w n / Real.sqrt n * (RHTower.riemannAutocorr (t + Real.log n) +
      RHTower.riemannAutocorr (t - Real.log n)) : ℝ) : ℂ)) =
      ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) *
        (((RHTower.riemannAutocorr (t - Real.log n) : ℝ) : ℂ) +
          ((RHTower.riemannAutocorr (t + Real.log n) : ℝ) : ℂ)) := by
    congr 1; funext n; push_cast; ring
  rw [hlhs, hRep]
  congr 1; funext ξ
  rw [xiSq_ofReal_eq, hR.conj_line ξ, Complex.add_conj]
  unfold lineDensity
  push_cast; ring

theorem charFun_map_withDensity {f : ℝ → ℝ≥0} (hf : Measurable f) (t : ℝ) :
    charFun ((volume.withDensity fun ξ => (f ξ : ℝ≥0∞)).map fun ξ : ℝ => 2 * π * ξ) t =
      ∫ ξ : ℝ, cexp (2 * π * I * ξ * t) * ((f ξ : ℝ) : ℂ) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    integral_withDensity_eq_integral_smul hf]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]
  push_cast; ring_nf

/-- **The line density is nonpositive** when `−ψ_u` is positive definite. -/
theorem lineDensity_nonpos (hR : RegularDeviation w E) {A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ n, |w n / Real.sqrt n| ≤ A)
    (hPD : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      fun y => ((-nullPotential (fun n => w n / Real.sqrt n) y : ℝ) : ℂ)) (ξ₀ : ℝ) :
    lineDensity E ξ₀ ≤ 0 := by
  have hcont := continuous_nullPotential (u := fun n => w n / Real.sqrt n)
    (by simp [hR.zero]) hA hu
  obtain ⟨σ, hσf, hσ⟩ := GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite hPD
    (Complex.continuous_ofReal.comp hcont.neg)
  set h := lineDensity E with hh
  have hc : Continuous h := continuous_lineDensity hR
  have hi : Integrable h := integrable_lineDensity hR
  set fp : ℝ → ℝ≥0 := fun ξ => (-h ξ).toNNReal with hfp
  set fm : ℝ → ℝ≥0 := fun ξ => (h ξ).toNNReal with hfm
  have hfpm : Measurable fp := (hc.neg.measurable).real_toNNReal
  have hfmm : Measurable fm := hc.measurable.real_toNNReal
  set μp : Measure ℝ := (volume.withDensity fun ξ => (fp ξ : ℝ≥0∞)).map fun ξ : ℝ => 2 * π * ξ
  set μm : Measure ℝ := (volume.withDensity fun ξ => (fm ξ : ℝ≥0∞)).map fun ξ : ℝ => 2 * π * ξ
  have hfinp : IsFiniteMeasure (volume.withDensity fun ξ => (fp ξ : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.neg.hasFiniteIntegral
  have hfinm : IsFiniteMeasure (volume.withDensity fun ξ => (fm ξ : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have hchar : charFun (σ + μm) = charFun μp := by
    funext t
    have hint' : ∀ f : ℝ → ℝ≥0, Measurable f → (∀ ξ, (f ξ : ℝ) ≤ |h ξ|) →
        Integrable fun ξ : ℝ => cexp (2 * π * I * ξ * t) * ((f ξ : ℝ) : ℂ) := by
      intro f hf hle
      refine hi.norm.mono' (by fun_prop) (Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, norm_cexp_two_pi_I_mul]
      simp [hle ξ]
    have hbd : ∀ ν : Measure ℝ, IsFiniteMeasure ν →
        Integrable (fun x : ℝ => cexp ((t : ℂ) * x * I)) ν := fun ν _ =>
      (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun x => by
        rw [Complex.norm_exp]; simp)
    rw [charFun_apply_real, integral_add_measure (hbd σ hσf) (hbd μm inferInstance),
      ← charFun_apply_real, ← charFun_apply_real, hσ, charFun_map_withDensity hfmm,
      charFun_map_withDensity hfpm]
    have hpot := nullPotential_eq_integral hR t
    have hle_m : ∀ ξ, (fm ξ : ℝ) ≤ |h ξ| := fun ξ => by
      simp only [hfm, Real.coe_toNNReal']; exact max_le (le_abs_self _) (abs_nonneg _)
    rw [Complex.ofReal_neg, hpot, ← integral_neg, ← integral_add _ (hint' fm hfmm hle_m)]
    · refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only [hfp, hfm, Real.coe_toNNReal']
      have hmax : max (-h ξ) 0 = max (h ξ) 0 - h ξ := by
        rcases le_total (h ξ) 0 with hle | hle
        · rw [max_eq_left (by linarith), max_eq_right hle]; ring
        · rw [max_eq_right (by linarith), max_eq_left hle]; ring
      rw [hmax]; push_cast; ring
    · refine (hi.norm.mono' ((by fun_prop : Continuous fun ξ : ℝ =>
          cexp (2 * π * I * ξ * t)).mul (Complex.continuous_ofReal.comp hc)).aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)).neg
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [norm_mul, norm_cexp_two_pi_I_mul]
      simp
  have hmeq : σ + μm = μp := Measure.ext_of_charFun hchar
  by_contra hpos
  push Not at hpos
  set Aset : Set ℝ := {ξ | 0 < h ξ} with hAset
  have hAo : IsOpen Aset := isOpen_lt continuous_const hc
  set S : Set ℝ := {x | 0 < h (x / (2 * π))} with hS
  have hSo : IsOpen S := isOpen_lt continuous_const (hc.comp (by fun_prop))
  have hpre : (fun ξ : ℝ => 2 * π * ξ) ⁻¹' S = Aset := by
    ext ξ
    simp only [hS, hAset, mem_preimage, mem_setOf_eq]
    rw [show 2 * π * ξ / (2 * π) = ξ by field_simp]
  have hμp : μp S = 0 := by
    rw [Measure.map_apply (by fun_prop) hSo.measurableSet, hpre,
      withDensity_apply_eq_zero (by fun_prop)]
    convert measure_empty (μ := volume)
    ext ξ
    simp only [mem_inter_iff, mem_setOf_eq, ne_eq, ENNReal.coe_eq_zero, hAset, hfp,
      Real.toNNReal_eq_zero, mem_empty_iff_false, iff_false, not_and]
    intro _ hξ; linarith
  have hμm : μm S = 0 := by
    have h2 := congrArg (fun ν : Measure ℝ => ν S) hmeq
    simp only [Measure.add_apply] at h2
    rw [hμp] at h2
    exact (add_eq_zero.mp h2).2
  rw [Measure.map_apply (by fun_prop) hSo.measurableSet, hpre,
    withDensity_apply_eq_zero (by fun_prop)] at hμm
  have hAz : volume Aset = 0 := by
    convert hμm using 2
    ext ξ
    simp only [mem_inter_iff, mem_setOf_eq, ne_eq, ENNReal.coe_eq_zero, hAset, hfm,
      Real.toNNReal_eq_zero, not_le]
    constructor
    · intro hξ; exact ⟨hξ, hξ⟩
    · intro hξ; exact hξ.2
  rw [IsOpen.measure_eq_zero_iff volume hAo] at hAz
  have : ξ₀ ∈ Aset := hpos
  rw [hAz] at this
  exact this

/-- **`Re E ≤ 0` on the critical line.** -/
theorem re_E_nonpos (hR : RegularDeviation w E) {A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ n, |w n / Real.sqrt n| ≤ A)
    (hPD : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      fun y => ((-nullPotential (fun n => w n / Real.sqrt n) y : ℝ) : ℂ)) (ξ₀ : ℝ) :
    (E (1 / 2 + 2 * π * I * ξ₀)).re ≤ 0 := by
  refine nonpos_of_nonpos_off_zeros differentiable_xiSq xiSq_zero_ne
    (Complex.continuous_re.comp (continuous_E_line hR)) (fun ξ hξ => ?_) ξ₀
  have hd := lineDensity_nonpos hR hA hu hPD ξ
  have hx : 0 < RHTower.WeilExcess.riemannXiReal ξ ^ 2 := by
    rw [xiSq_ofReal_eq] at hξ
    have : RHTower.WeilExcess.riemannXiReal ξ ^ 2 ≠ 0 := by exact_mod_cast hξ
    positivity
  unfold lineDensity at hd
  show (E (1 / 2 + 2 * π * I * ξ)).re ≤ 0
  nlinarith

/-! ## Annihilation and vanishing -/

theorem liftC_supp {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    ∀ u, liftC g u ≠ 0 → |u| ≤ 1 / 4 := by
  intro u hu
  by_contra h
  exact hu (by simp [liftC, hsupp u (not_le.mp h)])

theorem weilTest_liftC_narrowG (m : ℕ) (x : ℝ) :
    EF.weilTest (liftC (narrowG m)) (liftC (narrowG m)) x =
      ((autoCorr (narrowG m) x : ℝ) : ℂ) :=
  weilTest_liftC (narrowG m) x

theorem paperFT_liftC_zero (g : ℝ → ℝ) : paperFT (liftC g) 0 = ((∫ u, g u : ℝ) : ℂ) := by
  rw [paperFT, ← integral_complex_ofReal]
  congr 1; funext u; simp [liftC]

/-- **The continuation is purely imaginary on the critical line.** -/
theorem re_E_eq_zero (hR : RegularDeviation w E) {A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ n, |w n / Real.sqrt n| ≤ A)
    (hPD : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      fun y => ((-nullPotential (fun n => w n / Real.sqrt n) y : ℝ) : ℂ)) (ξ₀ : ℝ) :
    (E (1 / 2 + 2 * π * I * ξ₀)).re = 0 := by
  set f := liftC (narrowG 0) with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_liftC (contDiff_narrowG 0)
  have hfc : HasCompactSupport f := hasCompactSupport_liftC (hasCompactSupport_narrowG 0)
  have hsupp := narrowG_supp 0
  obtain ⟨C, hC0, hC⟩ := exists_norm_pairTransform_le hf hfc (liftC_supp hsupp)
  obtain ⟨CE, hCE, hEb⟩ := hR.growth
  have hRep := tsum_deviation_mul_pair_eq (G := pairTransform f) (g := EF.weilTest f f)
    hR.zero hR.summable hR.series hR.differentiableAt hCE hEb hC0
    (fun z _ => differentiable_pairTransform hf hfc z) hC
    (weilTest_eq_integral hf hfc (liftC_supp hsupp)) 0
  have hlhs : ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) *
      (EF.weilTest f f ((0 : ℝ) - Real.log n) + EF.weilTest f f ((0 : ℝ) + Real.log n)) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> simp [hR.zero, hR.one]
    · have hlog : 1 / 2 < Real.log n := by
        have := Real.log_le_log two_pos (by exact_mod_cast h : (2 : ℝ) ≤ n)
        linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]
      rw [hfdef, weilTest_liftC_narrowG, weilTest_liftC_narrowG,
        autoCorr_eq_zero hsupp (x := (0 : ℝ) - Real.log n)
          (by rw [zero_sub, abs_neg, abs_of_pos (by linarith)]; exact hlog),
        autoCorr_eq_zero hsupp (x := (0 : ℝ) + Real.log n)
          (by rw [zero_add, abs_of_pos (by linarith)]; exact hlog)]
      simp
  rw [hlhs] at hRep
  set P : ℝ → ℝ := fun ξ => ‖paperFT f (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  set q : ℝ → ℝ := fun ξ => P ξ * (E (1 / 2 + 2 * π * I * ξ)).re with hq
  have hq_eq : ∀ ξ : ℝ, pairTransform f ξ * cexp (2 * π * I * ξ * ((0 : ℝ) : ℂ)) *
      (E (1 / 2 + 2 * π * I * ξ) + E (1 / 2 - 2 * π * I * ξ)) = ((2 * q ξ : ℝ) : ℂ) := by
    intro ξ
    rw [pairTransform_ofReal hf hfc, hR.conj_line, Complex.add_conj]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hq, hP]
    push_cast; ring
  simp_rw [hq_eq, integral_complex_ofReal] at hRep
  have hint : ∫ ξ, q ξ = 0 := by
    have h2 : (∫ ξ, 2 * q ξ) = 0 := by exact_mod_cast hRep.symm
    rw [integral_const_mul] at h2
    linarith
  have hPc : Continuous P :=
    (((Zeta23.WeilEF.differentiable_paperFT hf.continuous hfc).continuous.comp
      (by fun_prop)).norm).pow 2
  have hqc : Continuous q :=
    hPc.mul (Complex.continuous_re.comp (continuous_E_line hR))
  have hq_nonpos : ∀ ξ, q ξ ≤ 0 := fun ξ =>
    mul_nonpos_of_nonneg_of_nonpos (by simp only [hP]; positivity)
      (re_E_nonpos hR hA hu hPD ξ)
  have hqi : Integrable q := by
    refine (integrable_inv_one_add_sq.const_mul (C * CE * (2 * π))).mono'
      hqc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    have hb := hC (ξ : ℂ) (by simp [shiftHeight_pos.le])
    rw [pairTransform_ofReal hf hfc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hb
    simp only [Complex.ofReal_re] at hb
    have hE := hEb (1 / 2 + 2 * π * I * ξ) (by simp) (by simp; norm_num)
    have him : |(1 / 2 + 2 * π * I * ξ : ℂ).im| = 2 * π * |ξ| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [him] at hE
    have hre : |(E (1 / 2 + 2 * π * I * ξ)).re| ≤ CE * (1 + 2 * π * |ξ|) :=
      (Complex.abs_re_le_norm _).trans hE
    have hk := inv_one_add_abs_pow_three_mul_le ξ
    rw [Real.norm_eq_abs, hq, abs_mul, abs_of_nonneg (by simp only [hP]; positivity)]
    calc P ξ * |(E (1 / 2 + 2 * π * I * ξ)).re|
        ≤ C * ((1 + |ξ|) ^ 3)⁻¹ * (CE * (1 + 2 * π * |ξ|)) := by gcongr
      _ = C * CE * (((1 + |ξ|) ^ 3)⁻¹ * (1 + 2 * π * |ξ|)) := by ring
      _ ≤ C * CE * (2 * π * (1 + ξ ^ 2)⁻¹) := by gcongr
      _ = C * CE * (2 * π) * (1 + ξ ^ 2)⁻¹ := by ring
  have hae : (fun ξ => -q ξ) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ξ => neg_nonneg.mpr (hq_nonpos ξ)) hqi.neg).mp
      (by rw [integral_neg, hint, neg_zero])
  have hq0 : ∀ ξ, q ξ = 0 := by
    have h := (Continuous.ae_eq_iff_eq volume hqc.neg continuous_const).mp hae
    intro ξ
    exact neg_eq_zero.mp (congrFun h ξ)
  have hF1 : paperFT f (-(2 * π * (0 : ℂ))) ≠ 0 := by
    rw [mul_zero, neg_zero, hfdef, paperFT_liftC_zero]
    have hpos : 0 < ∫ u, narrowG 0 u := (narrowBump 0).integral_pos
    exact_mod_cast hpos.ne'
  refine eq_zero_of_eq_zero_off_zeros (F := fun z => paperFT f (-(2 * π * z)))
    ((Zeta23.WeilEF.differentiable_paperFT hf.continuous hfc).comp (by fun_prop)) hF1
    (Complex.continuous_re.comp (continuous_E_line hR)) (fun ξ hξ => ?_) ξ₀
  have h := hq0 ξ
  simp only [hq, hP] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))

theorem windowValue_narrowG_log {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    windowValue (narrowG m) (Real.log m) n =
      if n = m then autoCorr (narrowG m) 0 / Real.sqrt m else 0 := by
  have h := congrArg (fun f : LogIndex →₀ ℝ => f ⟨n, hn⟩) (windowVector_narrowG hm)
  simp only [windowVector, Finsupp.ofSupportFinite_coe] at h
  rw [h, Finsupp.single_apply]
  by_cases hnm : n = m
  · subst hnm; simp
  · rw [if_neg (fun h' => hnm (congrArg Subtype.val h').symm), if_neg hnm]

/-- **Near-null regular rigidity.** A regular deviation `w = u√n` with bounded `u` whose null
potential `−ψ_u` is positive definite vanishes. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential (hR : RegularDeviation w E) {A : ℝ}
    (hA : 0 ≤ A) (hu : ∀ n, |w n / Real.sqrt n| ≤ A)
    (hPD : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      fun y => ((-nullPotential (fun n => w n / Real.sqrt n) y : ℝ) : ℂ)) (m : ℕ) : w m = 0 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl
    · exact hR.zero
    · exact hR.one
  set f := liftC (narrowG m) with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_liftC (contDiff_narrowG m)
  have hfc : HasCompactSupport f := hasCompactSupport_liftC (hasCompactSupport_narrowG m)
  obtain ⟨C, hC0, hC⟩ := exists_norm_pairTransform_le hf hfc (liftC_supp (narrowG_supp m))
  obtain ⟨CE, hCE, hEb⟩ := hR.growth
  have hRep := tsum_deviation_mul_pair_eq (G := pairTransform f) (g := EF.weilTest f f)
    hR.zero hR.summable hR.series hR.differentiableAt hCE hEb hC0
    (fun z _ => differentiable_pairTransform hf hfc z) hC
    (weilTest_eq_integral hf hfc (liftC_supp (narrowG_supp m))) (Real.log m)
  have hzero : ∀ ξ : ℝ, E (1 / 2 + 2 * π * I * ξ) + E (1 / 2 - 2 * π * I * ξ) = 0 := by
    intro ξ
    rw [hR.conj_line, Complex.add_conj, re_E_eq_zero hR hA hu hPD ξ]
    simp
  simp_rw [hzero, mul_zero, integral_zero] at hRep
  have hterm : ∀ n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log m - Real.log n) + EF.weilTest f f (Real.log m + Real.log n)) =
      if n = m then ((w m * (autoCorr (narrowG m) 0 / Real.sqrt m) : ℝ) : ℂ) else 0 := by
    intro n
    rw [hfdef, weilTest_liftC_narrowG, weilTest_liftC_narrowG]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hnm : n ≠ m := by omega
      have : n = 0 ∨ n = 1 := by omega
      rw [if_neg hnm]
      rcases this with rfl | rfl <;> simp [hR.zero, hR.one]
    · have hwv := windowValue_narrowG_log hm hn
      have hsym : autoCorr (narrowG m) (Real.log m - Real.log n) =
          autoCorr (narrowG m) (Real.log n - Real.log m) := by
        rw [← autoCorr_neg, neg_sub]
      rw [hsym, add_comm (Real.log m) (Real.log n)]
      have hval : ((w n / Real.sqrt n : ℝ) : ℂ) *
          (((autoCorr (narrowG m) (Real.log n - Real.log m) : ℝ) : ℂ) +
            ((autoCorr (narrowG m) (Real.log n + Real.log m) : ℝ) : ℂ)) =
          ((w n * windowValue (narrowG m) (Real.log m) n : ℝ) : ℂ) := by
        unfold windowValue; push_cast; ring
      rw [hval, hwv]
      split_ifs with hnm
      · subst hnm; rfl
      · simp
  rw [tsum_congr hterm, tsum_ite_eq] at hRep
  have hk0 : 0 < autoCorr (narrowG m) 0 / Real.sqrt m :=
    div_pos (autoCorr_narrowG_zero_pos m)
      (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m)))
  have h' : w m * (autoCorr (narrowG m) 0 / Real.sqrt m) = 0 := by exact_mod_cast hRep
  exact (mul_eq_zero.mp h').resolve_right hk0.ne'

theorem RegularDeviation.neg (hR : RegularDeviation w E) :
    RegularDeviation (fun n => -w n) (fun s => -E s) where
  zero := by simp [hR.zero]
  one := by simp [hR.one]
  summable := by simpa only [abs_neg] using hR.summable
  series := fun s hs => by
    rw [hR.series s hs, ← tsum_neg]
    congr 1; funext n; push_cast; ring
  differentiableAt := fun s h1 h2 => (hR.differentiableAt s h1 h2).neg
  growth := by
    obtain ⟨C, hC, hb⟩ := hR.growth
    exact ⟨C, hC, fun s h1 h2 => by rw [norm_neg]; exact hb s h1 h2⟩
  conj_line := fun ξ => by rw [hR.conj_line, map_neg]

theorem nullPotential_neg (u : ℕ → ℝ) (y : ℝ) :
    nullPotential (fun n => -u n) y = -nullPotential u y := by
  unfold nullPotential
  rw [← tsum_neg]
  congr 1; funext n; ring

/-- **Near-null regular rigidity, other sign.** If `+ψ_u` is positive definite, `u = 0`. -/
theorem eq_zero_of_positiveDefinite_nullPotential (hR : RegularDeviation w E) {A : ℝ}
    (hA : 0 ≤ A) (hu : ∀ n, |w n / Real.sqrt n| ≤ A)
    (hPD : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      fun y => ((nullPotential (fun n => w n / Real.sqrt n) y : ℝ) : ℂ)) (m : ℕ) : w m = 0 := by
  have hPD' : GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      fun y => ((-nullPotential (fun n => -w n / Real.sqrt n) y : ℝ) : ℂ) := by
    have e : ∀ y, -nullPotential (fun n => -w n / Real.sqrt n) y =
        nullPotential (fun n => w n / Real.sqrt n) y := fun y => by
      rw [show (fun n => -w n / Real.sqrt n) = fun n => -(w n / Real.sqrt n) from
        funext fun n => neg_div _ _, nullPotential_neg, neg_neg]
    simp_rw [e]; exact hPD
  have h := eq_zero_of_positiveDefinite_neg_nullPotential hR.neg hA
    (fun n => by rw [neg_div, abs_neg]; exact hu n) hPD' m
  simpa using h

end

end RHTower.WeilRegular
