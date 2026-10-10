import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver

/-!
# The vertical variance of the single-line HCF receiver

On the vertical line `Re τ = a` RH is equivalent to boundedness of the Xi heat trace
`ν(a + ib) = Σ_q exp(-(a + ib) w_q)`, `w_q = z_q²`
(`riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line`).  Under RH every `w_q` is a
positive real `λ_q`, and `b ↦ ν(a+ib)` is an absolutely convergent almost periodic function with
frequencies `λ_q`.

**Theorem** (`tendsto_xiGaussianHeatVerticalVariance_of_rh`).  Under RH, for every `a > 0`,

`(1/B) ∫₀^B ‖ν(a+ib)‖² db  →  Σ_{(q,q') : λ_q = λ_{q'}} exp(-a(λ_q + λ_{q'}))`   as `B → ∞`.

This is the vertical variance law (Bohr–Parseval).  The limit counts coincidences among the squared
ordinates `γ²`, weighted by `e^{-2aγ²}`.  The pair `±γ` always gives two copies with the same `λ`, and
multiple zeros give more, so the limit measures zero multiplicities.

**Theorem** (`mult_one_iff_tendsto_xiGaussianHeatVerticalVariance_of_rh`).  Under RH, all zeros of
`ξ` are simple iff the vertical variance tends to `2 Σ_q e^{-2aλ_q}`.  The coincidence sum equals
twice its diagonal exactly when every fibre of `q ↦ λ_q` is `{q, reflect q}`
(`vertical_variance_limit_eq_two_diag_iff`).

Mechanism: `‖ν‖² = Σ_{(q,q')} e^{-a(λ_q+λ_{q'})} cos(b(λ_q - λ_{q'}))` (Cauchy product of absolutely
summable families).  Integrate term by term (summable integral norms); the Fejér-type average
`(1/B)∫₀^B cos(bΔ) db` tends to `[Δ = 0]`, so dominated convergence applies.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The real part of the squared spectral coordinate (`= γ² - δ²`; under RH, `= γ²`). -/
def xiSpectralSqRe (q : XiZeroCopy) : ℝ := (xiSpectralPoint q ^ (2 : ℕ)).re

/-- The vertical variance of the heat trace on `Re τ = a` over `b ∈ [0, B]`. -/
def xiGaussianHeatVerticalVariance (a B : ℝ) : ℝ :=
  (1 / B) * ∫ b in (0 : ℝ)..B, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ^ 2

/-- The Fejér-type average of `cos(Δ b)` over `[0, B]`. -/
theorem integral_cos_mul_zero_eq (B Δ : ℝ) :
    ∫ b in (0 : ℝ)..B, Real.cos (Δ * b) = if Δ = 0 then B else Real.sin (Δ * B) / Δ := by
  split_ifs with hΔ
  · subst hΔ; simp
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hΔ, integral_cos, mul_zero,
      Real.sin_zero, sub_zero, smul_eq_mul, div_eq_inv_mul]

theorem abs_integral_cos_mul_zero_le {B : ℝ} (hB : 0 ≤ B) (Δ : ℝ) :
    |∫ b in (0 : ℝ)..B, Real.cos (Δ * b)| ≤ B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := B) (C := 1)
    (f := fun b => Real.cos (Δ * b)) (fun x _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hB, one_mul] at h
  exact h

theorem tendsto_fejer_cos (Δ : ℝ) :
    Tendsto (fun B : ℝ => 1 / B * ∫ b in (0 : ℝ)..B, Real.cos (Δ * b)) atTop
      (𝓝 (if Δ = 0 then 1 else 0)) := by
  by_cases hΔ : Δ = 0
  · rw [if_pos hΔ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    rw [integral_cos_mul_zero_eq, if_pos hΔ, one_div, inv_mul_cancel₀ hB.ne']
  · rw [if_neg hΔ]
    have hlim : Tendsto (fun B : ℝ => (1 / |Δ|) / B) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    rw [integral_cos_mul_zero_eq, if_neg hΔ, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity),
      abs_div]
    have hs : |Real.sin (Δ * B)| ≤ 1 := Real.abs_sin_le_one _
    have hΔ0 : 0 < |Δ| := abs_pos.2 hΔ
    calc 1 / B * (|Real.sin (Δ * B)| / |Δ|) ≤ 1 / B * (1 / |Δ|) := by gcongr
      _ = 1 / |Δ| / B := by ring

/-- Under RH the squared spectral coordinate is the real number `λ_q`. -/
theorem xiSpectralSq_eq_ofReal_xiSpectralSqRe_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiSpectralPoint q ^ (2 : ℕ) = ((xiSpectralSqRe q : ℝ) : ℂ) :=
  xiSpectralSq_eq_ofReal_re_of_rh hRH q

theorem xiSpectralSqRe_pos (q : XiZeroCopy) : 0 < xiSpectralSqRe q := by
  have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
  have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have := xiSpectralPoint_ne_zero q
    positivity
  rw [xiSpectralSqRe]; linarith

/-- Under RH the squared modulus of the vertical trace is the Cauchy-product cosine series. -/
theorem sq_norm_xiGaussianHeatTraceC_eq_of_rh (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a)
    (b : ℝ) :
    ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ^ 2 =
      ∑' p : XiZeroCopy × XiZeroCopy,
        Real.exp (-(a * xiSpectralSqRe p.1)) * Real.exp (-(a * xiSpectralSqRe p.2)) *
          Real.cos ((xiSpectralSqRe p.1 - xiSpectralSqRe p.2) * b) := by
  set τ : ℂ := (a : ℂ) + b * I
  have hτ : 0 < τ.re := by simpa [τ] using ha
  set f : XiZeroCopy → ℂ := fun q => xiGaussianHeatTermC τ q
  have hf : Summable (fun q => ‖f q‖) := summable_norm_xiGaussianHeatTermC hτ
  have hfc : Summable (fun q => ‖(starRingEnd ℂ) (f q)‖) := by
    simpa only [Complex.norm_conj] using hf
  have hprod := tsum_mul_tsum_of_summable_norm hf hfc
  have hsumm := summable_mul_of_summable_norm hf hfc
  have hsq : ‖xiGaussianHeatTraceC τ‖ ^ 2 =
      (xiGaussianHeatTraceC τ * (starRingEnd ℂ) (xiGaussianHeatTraceC τ)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  rw [hsq, xiGaussianHeatTraceC, Complex.conj_tsum, hprod, Complex.re_tsum hsumm]
  refine tsum_congr fun p => ?_
  simp only [f]
  rw [xiGaussianHeatTermC, xiGaussianHeatTermC, xiSpectralSq_eq_ofReal_xiSpectralSqRe_of_rh hRH,
    xiSpectralSq_eq_ofReal_xiSpectralSqRe_of_rh hRH, ← Complex.exp_conj, ← Complex.exp_add,
    Complex.exp_re]
  set l₁ := xiSpectralSqRe p.1
  set l₂ := xiSpectralSqRe p.2
  have hre : (-τ * (l₁ : ℂ) + (starRingEnd ℂ) (-τ * (l₂ : ℂ))).re = -(a * l₁) + -(a * l₂) := by
    simp [τ, Complex.mul_re]
  have him : (-τ * (l₁ : ℂ) + (starRingEnd ℂ) (-τ * (l₂ : ℂ))).im = -((l₁ - l₂) * b) := by
    simp [τ, Complex.mul_im]; ring
  rw [hre, him, Real.cos_neg, Real.exp_add]

/-- **Vertical variance law under RH.** -/
theorem tendsto_xiGaussianHeatVerticalVariance_of_rh (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun B => xiGaussianHeatVerticalVariance a B) atTop
      (𝓝 (∑' p : XiZeroCopy × XiZeroCopy,
        if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then
          Real.exp (-(a * xiSpectralSqRe p.1)) * Real.exp (-(a * xiSpectralSqRe p.2))
        else 0)) := by
  set c : XiZeroCopy → ℝ := fun q => Real.exp (-(a * xiSpectralSqRe q))
  have hc : Summable c := by
    have h := summable_norm_xiGaussianHeatTermC (τ := (a : ℂ)) (by simpa using ha)
    refine h.congr fun q => ?_
    rw [norm_xiGaussianHeatTermC]
    simp [c, xiSpectralSqRe]
  have hcn : Summable (fun q => ‖c q‖) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), c] using hc
  have hcc : Summable (fun p : XiZeroCopy × XiZeroCopy => c p.1 * c p.2) :=
    summable_mul_of_summable_norm hcn hcn
  set Δ : XiZeroCopy × XiZeroCopy → ℝ := fun p => xiSpectralSqRe p.1 - xiSpectralSqRe p.2
  set G : XiZeroCopy × XiZeroCopy → ℝ → ℝ := fun p b => c p.1 * c p.2 * Real.cos (Δ p * b)
  -- term-by-term integration
  have hint : ∀ B : ℝ, 0 ≤ B →
      (∫ b in (0 : ℝ)..B, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ^ 2) =
        ∑' p, c p.1 * c p.2 * ∫ b in (0 : ℝ)..B, Real.cos (Δ p * b) := by
    intro B hB
    have hcongr : (fun b : ℝ => ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ^ 2) =
        fun b => ∑' p, G p b := by
      funext b
      rw [sq_norm_xiGaussianHeatTraceC_eq_of_rh hRH ha b]
    rw [hcongr, intervalIntegral.integral_of_le hB]
    have hGint : ∀ p, Integrable (G p) (volume.restrict (Ioc 0 B)) := fun p =>
      (by fun_prop : Continuous (G p)).integrableOn_Ioc
    have hGsum : Summable (fun p => ∫ b in Ioc 0 B, ‖G p b‖) := by
      refine (hcc.mul_right B).of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _)
        fun p => ?_
      have hle : (∫ b in Ioc 0 B, ‖G p b‖) ≤ ∫ b in Ioc 0 B, c p.1 * c p.2 := by
        refine setIntegral_mono_on (hGint p).norm (by fun_prop : Continuous fun _ : ℝ =>
          c p.1 * c p.2).integrableOn_Ioc measurableSet_Ioc fun b _ => ?_
        simp only [G, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), c]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
      rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
        sub_zero, smul_eq_mul] at hle
      linarith
    rw [← integral_tsum_of_summable_integral_norm hGint hGsum]
    refine tsum_congr fun p => ?_
    rw [← intervalIntegral.integral_of_le hB, ← intervalIntegral.integral_const_mul]
  have hrepr : ∀ᶠ B : ℝ in atTop, xiGaussianHeatVerticalVariance a B =
      ∑' p, c p.1 * c p.2 * (1 / B * ∫ b in (0 : ℝ)..B, Real.cos (Δ p * b)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    rw [xiGaussianHeatVerticalVariance, hint B hB, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    ring
  have hlim : Tendsto (fun B : ℝ => ∑' p, c p.1 * c p.2 *
      (1 / B * ∫ b in (0 : ℝ)..B, Real.cos (Δ p * b))) atTop
      (𝓝 (∑' p, c p.1 * c p.2 * (if Δ p = 0 then 1 else 0))) := by
    refine tendsto_tsum_of_dominated_convergence hcc (fun p => ?_) ?_
    · exact (tendsto_fejer_cos (Δ p)).const_mul _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB p
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < c p.1 * c p.2)]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / B)]
      have := abs_integral_cos_mul_zero_le hB.le (Δ p)
      calc 1 / B * |∫ b in (0 : ℝ)..B, Real.cos (Δ p * b)| ≤ 1 / B * B := by gcongr
        _ = 1 := by field_simp
  have hval : (∑' p, c p.1 * c p.2 * (if Δ p = 0 then 1 else 0)) =
      ∑' p : XiZeroCopy × XiZeroCopy,
        if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then
          Real.exp (-(a * xiSpectralSqRe p.1)) * Real.exp (-(a * xiSpectralSqRe p.2))
        else 0 := by
    refine tsum_congr fun p => ?_
    simp only [Δ, sub_eq_zero, c]
    split_ifs <;> simp
  rw [← hval]
  exact hlim.congr' (hrepr.mono fun B hB => hB.symm)

/-- The vertical variance limit dominates its diagonal `Σ_q e^{-2aλ_q}`, so it is at least the heat
trace at real time `2a`. -/
theorem tsum_diag_le_vertical_variance_limit {a : ℝ} (ha : 0 < a) :
    (∑' q : XiZeroCopy, Real.exp (-(a * xiSpectralSqRe q)) * Real.exp (-(a * xiSpectralSqRe q))) ≤
      ∑' p : XiZeroCopy × XiZeroCopy,
        if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then
          Real.exp (-(a * xiSpectralSqRe p.1)) * Real.exp (-(a * xiSpectralSqRe p.2))
        else 0 := by
  set c : XiZeroCopy → ℝ := fun q => Real.exp (-(a * xiSpectralSqRe q))
  have hc : Summable c := by
    have h := summable_norm_xiGaussianHeatTermC (τ := (a : ℂ)) (by simpa using ha)
    refine h.congr fun q => ?_
    rw [norm_xiGaussianHeatTermC]
    simp [c, xiSpectralSqRe]
  have hcn : Summable (fun q => ‖c q‖) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), c] using hc
  have hcc : Summable (fun p : XiZeroCopy × XiZeroCopy => c p.1 * c p.2) :=
    summable_mul_of_summable_norm hcn hcn
  set F : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then c p.1 * c p.2 else 0
  have hF0 : ∀ p, 0 ≤ F p := fun p => by
    simp only [F]; split_ifs <;> positivity
  have hF : Summable F := hcc.of_nonneg_of_le hF0 fun p => by
    simp only [F]; split_ifs
    · exact le_rfl
    · positivity
  have hinj : Function.Injective (fun q : XiZeroCopy => (q, q)) := fun x y h => (Prod.mk.inj h).1
  have h := tsum_comp_le_tsum_of_inj hF hF0 hinj
  simp only [F, Function.comp_def, if_true, c] at h
  exact h

/-! ## Simple zeros ⇔ the variance equals twice the diagonal -/

/-- Every fibre of `q ↦ λ_q` is exactly `{q, reflect q}`. -/
def XiSpectralSqFiberMinimal : Prop :=
  ∀ q q' : XiZeroCopy, xiSpectralSqRe q = xiSpectralSqRe q' →
    q' = q ∨ q' = xiZeroCopyReflectEquiv q

theorem xiSpectralSqRe_reflect (q : XiZeroCopy) :
    xiSpectralSqRe (xiZeroCopyReflectEquiv q) = xiSpectralSqRe q := by
  rw [xiSpectralSqRe, xiSpectralSqRe, xiSpectralPoint_reflect, neg_sq]

/-- **Variance-diagonal identity.**  For `a > 0` the coincidence sum
`L(a) = Σ_{λ_q = λ_q'} e^{-a(λ_q+λ_q')}` equals `2 Σ_q e^{-2aλ_q}` iff every `λ`-fibre is `{q, reflect q}`. -/
theorem vertical_variance_limit_eq_two_diag_iff {a : ℝ} (ha : 0 < a) :
    (∑' p : XiZeroCopy × XiZeroCopy,
        if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then
          Real.exp (-(a * xiSpectralSqRe p.1)) * Real.exp (-(a * xiSpectralSqRe p.2))
        else 0) =
      2 * ∑' q : XiZeroCopy, Real.exp (-(a * xiSpectralSqRe q)) * Real.exp (-(a * xiSpectralSqRe q))
      ↔ XiSpectralSqFiberMinimal := by
  classical
  set c : XiZeroCopy → ℝ := fun q => Real.exp (-(a * xiSpectralSqRe q))
  have hcpos : ∀ q, 0 < c q := fun q => Real.exp_pos _
  have hc : Summable c := by
    have h := summable_norm_xiGaussianHeatTermC (τ := (a : ℂ)) (by simpa using ha)
    refine h.congr fun q => ?_
    rw [norm_xiGaussianHeatTermC]
    simp [c, xiSpectralSqRe]
  have hcn : Summable (fun q => ‖c q‖) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), c] using hc
  have hcc : Summable (fun p : XiZeroCopy × XiZeroCopy => c p.1 * c p.2) :=
    summable_mul_of_summable_norm hcn hcn
  have hcrefl : ∀ q, c (xiZeroCopyReflectEquiv q) = c q := fun q => by
    simp only [c, xiSpectralSqRe_reflect]
  set F : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then c p.1 * c p.2 else 0
  have hF0 : ∀ p, 0 ≤ F p := fun p => by
    simp only [F]; split_ifs
    · exact (mul_pos (hcpos _) (hcpos _)).le
    · exact le_rfl
  have hF : Summable F := hcc.of_nonneg_of_le hF0 fun p => by
    simp only [F]; split_ifs
    · exact le_rfl
    · exact (mul_pos (hcpos _) (hcpos _)).le
  -- inner sums
  set I : XiZeroCopy → XiZeroCopy → ℝ := fun q q' =>
    if xiSpectralSqRe q = xiSpectralSqRe q' then c q' else 0
  have hI0 : ∀ q q', 0 ≤ I q q' := fun q q' => by
    simp only [I]; split_ifs
    · exact (hcpos _).le
    · exact le_rfl
  have hIs : ∀ q, Summable (I q) := fun q => hc.of_nonneg_of_le (hI0 q) fun q' => by
    simp only [I]; split_ifs
    · exact le_rfl
    · exact (hcpos _).le
  set E : XiZeroCopy → XiZeroCopy → ℝ := fun q q' =>
    if q' = xiZeroCopyReflectEquiv q then 0 else if q' = q then 0 else I q q'
  have hE0 : ∀ q q', 0 ≤ E q q' := fun q q' => by
    simp only [E]; split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact hI0 q q'
  have hsplit : ∀ q, ∑' q', I q q' = 2 * c q + ∑' q', E q q' := by
    intro q
    have hne : xiZeroCopyReflectEquiv q ≠ q := xiZeroCopyReflectEquiv_ne q
    have h1 := (hIs q).tsum_eq_add_tsum_ite q
    have hs2 : Summable (fun q' => if q' = q then 0 else I q q') :=
      (hIs q).of_nonneg_of_le (fun q' => by split_ifs; exacts [le_rfl, hI0 q q'])
        fun q' => by split_ifs; exacts [hI0 q q', le_rfl]
    have h2 := hs2.tsum_eq_add_tsum_ite (xiZeroCopyReflectEquiv q)
    have hIq : I q q = c q := by simp [I]
    have hIr : I q (xiZeroCopyReflectEquiv q) = c q := by
      simp only [I, xiSpectralSqRe_reflect, if_true, hcrefl]
    rw [h1, h2, hIq, if_neg hne, hIr]
    have hEeq : (∑' q', if q' = xiZeroCopyReflectEquiv q then 0 else
        (if q' = q then 0 else I q q')) = ∑' q', E q q' := rfl
    rw [hEeq]
    ring
  have hEs : ∀ q, Summable (E q) := fun q => (hIs q).of_nonneg_of_le (hE0 q) fun q' => by
    simp only [E]; split_ifs
    · exact hI0 q q'
    · exact hI0 q q'
    · exact le_rfl
  -- the product sum as an iterated sum
  have hrow : ∀ q, (∑' q', F (q, q')) = c q * ∑' q', I q q' := fun q => by
    rw [← (hIs q).tsum_mul_left]
    refine tsum_congr fun q' => ?_
    simp only [F, I]; split_ifs <;> ring
  have hprod : (∑' p, F p) = ∑' q, c q * ∑' q', I q q' := by
    rw [hF.tsum_prod]
    exact tsum_congr hrow
  have hrows : Summable (fun q => c q * ∑' q', I q q') :=
    hF.prod.congr hrow
  have hdiag : Summable (fun q => c q * c q) :=
    hc.of_nonneg_of_le (fun q => (mul_pos (hcpos q) (hcpos q)).le) fun q => by
      have : c q ≤ 1 := by
        simp only [c]; rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg ha.le (xiSpectralSqRe_pos q).le
      nlinarith [hcpos q]
  set d : XiZeroCopy → ℝ := fun q => c q * ∑' q', E q q'
  have hd0 : ∀ q, 0 ≤ d q := fun q => mul_nonneg (hcpos q).le (tsum_nonneg (hE0 q))
  have hdeq : ∀ q, d q = c q * ∑' q', I q q' - 2 * (c q * c q) := fun q => by
    simp only [d]; rw [hsplit q]; ring
  have hd : Summable d := by
    have := hrows.sub (hdiag.mul_left 2)
    exact this.congr fun q => (hdeq q).symm
  have hLeq : (∑' p, F p) = 2 * ∑' q, c q * c q + ∑' q, d q := by
    rw [hprod, ← hdiag.tsum_mul_left]
    rw [← (hdiag.mul_left 2).tsum_add hd]
    refine tsum_congr fun q => ?_
    rw [hdeq q]; ring
  have hFeq : (∑' p : XiZeroCopy × XiZeroCopy,
        if xiSpectralSqRe p.1 = xiSpectralSqRe p.2 then
          Real.exp (-(a * xiSpectralSqRe p.1)) * Real.exp (-(a * xiSpectralSqRe p.2))
        else 0) = ∑' p, F p := rfl
  have hDeq : (∑' q : XiZeroCopy, Real.exp (-(a * xiSpectralSqRe q)) *
      Real.exp (-(a * xiSpectralSqRe q))) = ∑' q, c q * c q := rfl
  rw [hFeq, hDeq, hLeq]
  constructor
  · intro h q q' hlam
    have hdz : (∑' q, d q) = 0 := by linarith
    have hdfun : d = 0 := (hasSum_zero_iff_of_nonneg hd0).1 (hdz ▸ hd.hasSum)
    have hdq : d q = 0 := congrFun hdfun q
    have hEsum : (∑' q', E q q') = 0 := by
      have := (mul_eq_zero.1 hdq)
      rcases this with h0 | h0
      · exact absurd h0 (hcpos q).ne'
      · exact h0
    have hEfun : E q = 0 := (hasSum_zero_iff_of_nonneg (hE0 q)).1 (hEsum ▸ (hEs q).hasSum)
    have hEq' : E q q' = 0 := congrFun hEfun q'
    by_contra hcon
    push Not at hcon
    have hval : E q q' = c q' := by
      simp only [E, I, if_neg hcon.2, if_neg hcon.1, if_pos hlam]
    rw [hval] at hEq'
    exact (hcpos q').ne' hEq'
  · intro hmin
    have hE : ∀ q q', E q q' = 0 := fun q q' => by
      simp only [E, I]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · rcases hmin q q' h3 with h | h
        · exact absurd h h2
        · exact absurd h h1
      · rfl
    have hdz : ∀ q, d q = 0 := fun q => by
      simp only [d]
      rw [show (fun q' => E q q') = fun _ => (0 : ℝ) from funext (hE q), tsum_zero, mul_zero]
    rw [show (fun q => d q) = fun _ => (0 : ℝ) from funext hdz, tsum_zero, add_zero]

/-- Under RH every `λ`-fibre is `{q, reflect q}` as soon as all zeros of `ξ` are simple. -/
theorem xiSpectralSqFiberMinimal_of_rh_of_mult_one (hRH : RiemannHypothesis)
    (hmult : ∀ ρ : XiDivisorSupport, Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) = 1) :
    XiSpectralSqFiberMinimal := by
  have hinj : Function.Injective xiSpectralPoint := by
    intro q r hqr
    have hbase : q.1 = r.1 := by
      apply xiSpectralPointSupport_injective
      simpa only [xiSpectralPoint_eq_support] using hqr
    apply Sigma.eq hbase
    haveI : Subsingleton
        (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (r.1 : ℂ)))) := by
      rw [hmult r.1]
      infer_instance
    apply Subsingleton.elim
  have him : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 :=
    (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH
  intro q q' hlam
  have hre : ∀ r : XiZeroCopy, xiSpectralSqRe r = (xiSpectralPoint r).re ^ 2 := fun r => by
    rw [xiSpectralSqRe, pow_two, Complex.mul_re, him r]; ring
  rw [hre, hre] at hlam
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hlam.symm with h | h
  · left
    apply hinj
    exact Complex.ext h (by rw [him, him])
  · right
    apply hinj
    rw [xiSpectralPoint_reflect]
    exact Complex.ext (by rw [Complex.neg_re]; exact h) (by rw [Complex.neg_im, him, him, neg_zero])

/-- Fibre-minimality forces every zero of `ξ` to be simple. -/
theorem mult_one_of_xiSpectralSqFiberMinimal (hmin : XiSpectralSqFiberMinimal)
    (ρ : XiDivisorSupport) : Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) = 1 := by
  have hpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
  by_contra hne
  have h2 : 1 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
  set q₀ : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  set q₁ : XiZeroCopy := ⟨ρ, ⟨1, h2⟩⟩
  have hsp : xiSpectralPoint q₁ = xiSpectralPoint q₀ := by
    simp only [xiSpectralPoint_eq_support, q₀, q₁]
  have hlam : xiSpectralSqRe q₀ = xiSpectralSqRe q₁ := by rw [xiSpectralSqRe, xiSpectralSqRe, hsp]
  rcases hmin q₀ q₁ hlam with h | h
  · have := congrArg (fun q : XiZeroCopy => (q.2 : ℕ)) h
    simp [q₀, q₁] at this
  · have hneg := congrArg xiSpectralPoint h
    rw [xiSpectralPoint_reflect, hsp] at hneg
    have hzero : xiSpectralPoint q₀ = 0 := by
      have : 2 * xiSpectralPoint q₀ = 0 := by linear_combination hneg
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    exact xiSpectralPoint_ne_zero q₀ hzero

/-- **Simple zeros from the vertical variance.**  Under RH, for every `a > 0`, all zeros of `ξ` are
simple iff the vertical variance of the heat trace on `Re τ = a` tends to `2 Σ_q e^{-2aλ_q}`. -/
theorem mult_one_iff_tendsto_xiGaussianHeatVerticalVariance_of_rh (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) :
    (∀ ρ : XiDivisorSupport, Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) = 1) ↔
      Tendsto (fun B => xiGaussianHeatVerticalVariance a B) atTop
        (𝓝 (2 * ∑' q : XiZeroCopy,
          Real.exp (-(a * xiSpectralSqRe q)) * Real.exp (-(a * xiSpectralSqRe q)))) := by
  have hlaw := tendsto_xiGaussianHeatVerticalVariance_of_rh hRH ha
  constructor
  · intro hmult
    have hmin := xiSpectralSqFiberMinimal_of_rh_of_mult_one hRH hmult
    rw [← (vertical_variance_limit_eq_two_diag_iff ha).2 hmin]
    exact hlaw
  · intro hlim
    have heq := tendsto_nhds_unique hlaw hlim
    exact mult_one_of_xiSpectralSqFiberMinimal ((vertical_variance_limit_eq_two_diag_iff ha).1 heq)

end

end RHTower
