import GaloisForLFunctions.RHTower.GaussianPrimeGapExponentLaw

/-!
# Explicit-constant Ω± for the Gaussian prime gap

For `0 < σ < ½` write `a = (½ − σ)/2` and `G(y) = Σ Λ(n) n^{-σ} e^{-yn²} − ∫₁^∞ u^{-σ} e^{-yu²} du`.

* **Residue bound** (`order_mul_norm_gamma_le_of_gaussianWeightedGap_le`).  If
  `η G(y) ≤ c y^{-a} + K` on `(0, 1]` (`η = ±1`), then RH holds and every critical zero `ρ₀` of
  order `m` satisfies `m |Γ((ρ₀ − σ)/2)| / 2 ≤ c`.  The deficit carrier (density
  `(c + ε)e^{au} − η G(e^{-u})`, made nonnegative off a compact set) is a nonnegative measure, so
  `|L(t + iτ)| ≤ L(t)` for real `t > a`; as `t ↓ a`, `(t − a)L(t) → c + ε` while
  `(t − a)L(t + iγ₀/2)` tends to the residue `η Γ((ρ₀ − σ)/2) m/2` of `ξ'/ξ(σ + 2w)`.
* **Unconditional Ω±** (`exists_pos_gaussianWeightedGap_omega`).  With Hardy's critical-line zeros,
  there is an explicit `c₀ > 0` such that `G` exceeds `c y^{-a} + K` and falls below
  `−(c y^{-a} + K)` on `(0, 1]` for every `c < c₀` and every `K`.  Under RH the exponent `a` is
  attained (`GaussianPrimeGapExponentLaw`), so the oscillation is exactly of order `y^{-(½−σ)/2}`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open GaloisForLFunctions.RHTower (laplaceMass complexLaplace IsAbscissa laplaceReal
  differentiableOn_complexLaplace complexLaplace_ofReal norm_complexLaplace_le)

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- A continuous function vanishing beyond `U` has finite Laplace mass at every exponent. -/
theorem integrableOn_mul_exp_of_eq_zero_of_le {f : ℝ → ℝ} (hf : Continuous f) {U : ℝ} (hU : 0 ≤ U)
    (hzero : ∀ u : ℝ, U ≤ u → f u = 0) (τ : ℝ) :
    IntegrableOn (fun u : ℝ => f u * Real.exp (-τ * u)) (Ioi 0) := by
  have hcont : Continuous fun u : ℝ => f u * Real.exp (-τ * u) := hf.mul (by fun_prop)
  rw [← Ioc_union_Ioi_eq_Ioi hU]
  refine IntegrableOn.union ((hcont.integrableOn_Icc (a := 0) (b := U)).mono_set
    Ioc_subset_Icc_self) ?_
  refine (integrableOn_zero (μ := volume) (s := Ioi U)).congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp [hzero u (le_of_lt hu)]

/-- **Ingham–Landau residue bound.**  Let `0 < σ < ½`, `a = (½ − σ)/2`, `η = ±1`, and let
`ρ₀ = ½ + iγ₀` be a zero of `ξ` of analytic order `m`.  If
`η (P_σ − C_σ)(y) ≤ c y^{-a} + K` on `(0, 1]`, then `m |Γ((ρ₀ − σ)/2)| / 2 ≤ c`.

The deficit carrier is a nonnegative measure, so `|L(t + iτ)| ≤ L(t)` for real `t > a`.  As
`t ↓ a`, `(t − a)L(t) → c + ε` (the reference pole) while `(t − a)L(t + iγ₀/2)` tends to the residue
`η Γ((ρ₀ − σ)/2) m/2` contributed by `ξ'/ξ(σ + 2w)` at `ρ₀`. -/
theorem order_mul_norm_gamma_le_of_gaussianWeightedGap_le {σ : ℝ} (hσ : 0 < σ)
    (hσ2 : σ < 1 / 2) {η : ℝ} (hη : η = 1 ∨ η = -1) {ρ₀ : ℂ} (hρ₀ : xi ρ₀ = 0)
    (hρ₀re : ρ₀.re = 1 / 2) {m : ℕ} (hm : analyticOrderAt xi ρ₀ = m) {c K : ℝ}
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 →
      η * (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ≤
        c * y ^ (-(1 / 2 - σ) / 2) + K) :
    (m : ℝ) * ‖Complex.Gamma ((ρ₀ - σ) / 2)‖ / 2 ≤ c := by
  set a : ℝ := (1 / 2 - σ) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have ha1 : a ≤ 1 := by rw [ha_def]; linarith
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hηabs : |η| ≤ 1 := by rcases hη with h | h <;> simp [h]
  have hη2 : (η : ℂ) * η = 1 := by rcases hη with h | h <;> simp [h]
  -- zero-free right of the critical line
  have hfree : ∀ z : ℂ, 1 / 2 < z.re → xi z ≠ 0 := by
    intro z hz
    refine xi_ne_zero_of_gaussianPrimeGrowthBudget hσ hη ha.le ha1 (B := |c| + |K|)
      (fun y hy hy1 => ?_) (by rw [ha_def]; linarith)
    have h1 := hB y hy hy1
    have hpow : 1 ≤ y ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
    have h2 : c * y ^ (-(1 / 2 - σ) / 2) ≤ |c| * y ^ (-a) := by
      rw [show -(1 / 2 - σ) / 2 = -a by rw [ha_def]; ring]
      exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    have h3 : K ≤ |K| * y ^ (-a) := le_trans (le_abs_self K)
      (le_mul_of_one_le_right (abs_nonneg K) hpow)
    linarith
  -- it suffices to beat `c + ε` for every `ε > 0`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set B' : ℝ := c + ε with hB'
  set h : ℝ → ℝ := gaussianBudgetProfile η σ a B' with hhdef
  have hc : Continuous h := continuous_gaussianBudgetProfile hσ η a B'
  set hN : ℝ → ℝ := fun u => max (-h u) 0 with hNdef
  have hNc : Continuous hN := hc.neg.max continuous_const
  -- the negative part vanishes beyond `U`
  set U : ℝ := |K| / (ε * a) with hU
  have hU0 : 0 ≤ U := by positivity
  have hNzero : ∀ u : ℝ, U ≤ u → hN u = 0 := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hU0 hu
    have hy := hB (Real.exp (-u)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
    rw [← Real.exp_mul, show -u * (-(1 / 2 - σ) / 2) = a * u by rw [ha_def]; ring] at hy
    have hexp : ε * (1 + a * u) ≤ ε * Real.exp (a * u) := by
      have := Real.add_one_le_exp (a * u); nlinarith
    have hKle : |K| ≤ ε * a * u := by
      have := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ ε * a)
      rw [hU, mul_div_cancel₀ _ (by positivity)] at this
      linarith
    have hK : K ≤ ε * Real.exp (a * u) := by
      have := le_abs_self K; nlinarith
    simp only [hNdef, hhdef, gaussianBudgetProfile]
    rw [max_eq_right]
    rw [hB']
    nlinarith [Real.exp_pos (a * u)]
  have hexc : ∀ τ : ℝ, a < τ → IntegrableOn
      (fun u : ℝ => max (-gaussianBudgetProfile η σ a B' u) 0 * Real.exp (-τ * u)) (Ioi 0) :=
    fun τ _ => integrableOn_mul_exp_of_eq_zero_of_le hNc hU0 hNzero τ
  -- the two carriers
  set νP : Measure ℝ := expThickenedCarrier fun u => max (gaussianBudgetProfile η σ a B' u) 0
    with hνP
  set νN : Measure ℝ := expThickenedCarrier hN with hνN
  obtain ⟨cP, hcP, hcPa⟩ := exists_isAbscissa_gaussianBudgetCarrier_le hσ hη ha.le ha1 B' hexc
  obtain ⟨cN, hcN, hcN0⟩ := exists_isAbscissa_expThickenedCarrier_le hNc
    (fun u _ => le_max_right _ _) le_rfl (fun τ _ => integrableOn_mul_exp_of_eq_zero_of_le
      hNc hU0 hNzero τ)
  have hLP : DifferentiableOn ℂ (complexLaplace νP) {w : ℂ | a < w.re} :=
    (differentiableOn_complexLaplace hcP).mono fun w hw => lt_of_le_of_lt hcPa hw
  have hLN : DifferentiableOn ℂ (complexLaplace νN) {w : ℂ | 0 < w.re} :=
    (differentiableOn_complexLaplace hcN).mono fun w hw => lt_of_le_of_lt hcN0 hw
  set T : ℂ → ℂ := mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ : ℂ))) with hT
  have hTd : Differentiable ℂ T := differentiable_mellin_indicator_gap hs
  -- the regular part of the continuation
  set R : ℂ → ℂ := fun w => -(η * (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
      logDeriv xi ((σ : ℂ) + 2 * w)) - T w)) + complexLaplace νN w with hR
  have hRd : ∀ w : ℂ, 0 < w.re → xi ((σ : ℂ) + 2 * w) ≠ 0 → DifferentiableAt ℂ R w := by
    intro w hw0 hxw
    have hre : 0 < ((σ : ℂ) + 2 * w).re := by simp; linarith
    have hΓ : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma w (fun k h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hA : DifferentiableAt ℂ (fun w : ℂ => gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w)) w :=
      (differentiableAt_gaussianArchimedeanCurrent hre).comp (f := fun w : ℂ => (σ : ℂ) + 2 * w) w
        (by fun_prop)
    have hL : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi ((σ : ℂ) + 2 * w)) w := by
      have hd : DifferentiableAt ℂ (fun ζ => deriv xi ζ / xi ζ) ((σ : ℂ) + 2 * w) :=
        ((xi_differentiable.analyticAt _).deriv.differentiableAt).div
          (xi_differentiable _) hxw
      exact hd.comp (f := fun w : ℂ => (σ : ℂ) + 2 * w) w (by fun_prop)
    have hN' : DifferentiableAt ℂ (complexLaplace νN) w :=
      hLN.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw0)
    exact (((differentiableAt_const _).mul ((hΓ.mul (hA.sub hL)).sub (hTd w))).neg).add hN'
  -- the transform equals `B'/(w − a) + R(w)` on `Re w > a`
  have hU : IsOpen {w : ℂ | a < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hxiU : ∀ w : ℂ, a < w.re → xi ((σ : ℂ) + 2 * w) ≠ 0 := by
    intro w hw
    exact hfree _ (by simp; rw [ha_def] at hw; linarith)
  have hΨd : DifferentiableOn ℂ (fun w => B' / (w - a) + R w) {w : ℂ | a < w.re} := by
    intro w hw
    have hwa : a < w.re := hw
    have hw0' : w - a ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact ((((differentiableAt_const _).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - (a : ℂ)) w) hw0')).add
      (hRd w (by linarith) (hxiU w hwa))).differentiableWithinAt
  have hagree : Set.EqOn (complexLaplace νP) (fun w => B' / (w - a) + R w) {w : ℂ | a < w.re} := by
    refine (hLP.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hΨd.analyticOnNhd hU)
      (convex_halfSpace_re_gt a).isPreconnected (z₀ := (4 : ℂ)) (by simp; linarith) ?_
    have hopen : IsOpen {w : ℂ | 3 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (3 : ℝ) < (4 : ℂ).re by norm_num)] with w hw
    rw [hνP, complexLaplace_gaussianBudgetCarrier_eq hσ hη ha1 B' hw]
    simp only [hR, hνN, hNdef, hhdef]
    ring
  -- positivity of the carrier along the vertical line through the zero
  set τ : ℝ := ρ₀.im / 2 with hτ
  set w₀ : ℂ := (ρ₀ - σ) / 2 with hw₀
  have hw₀eq : w₀ = (a : ℂ) + τ * I := by
    rw [hw₀, hτ, ha_def]
    apply Complex.ext <;> simp [hρ₀re]
  have hτ0 : τ ≠ 0 := by
    have him : 1 < |ρ₀.im| := by
      by_contra h; push Not at h; exact xi_ne_zero_of_abs_im_le_one h hρ₀
    rw [hτ]; intro h; rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rw [h] at him; simp at him; linarith
    · norm_num at h
  have hpos : ∀ t : ℝ, a < t → ‖complexLaplace νP ((t : ℂ) + τ * I)‖ ≤ laplaceReal νP t := by
    intro t ht
    have h := norm_complexLaplace_le νP ((t : ℂ) + τ * I)
    have hre : ((t : ℂ) + τ * I).re = t := by simp
    rw [hre] at h
    exact h
  -- the two limits
  have hRa : ContinuousAt R (a : ℂ) := by
    refine (hRd (a : ℂ) (by simpa using ha) ?_).continuousAt
    have hcast : (σ : ℂ) + 2 * (a : ℂ) = ((σ + 2 * a : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]; exact xi_ne_zero_of_real _
  have hlimR : Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ) * complexLaplace νP (t : ℂ)) (𝓝[>] a)
      (𝓝 (B' : ℂ)) := by
    have h1 : Tendsto (fun t : ℝ => (B' : ℂ) + ((t - a : ℝ) : ℂ) * R (t : ℂ)) (𝓝[>] a)
        (𝓝 ((B' : ℂ) + ((a - a : ℝ) : ℂ) * R (a : ℂ))) := by
      refine tendsto_const_nhds.add (Tendsto.mul ?_ ?_)
      · exact ((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).tendsto a).mono_left
          nhdsWithin_le_nhds
      · exact (hRa.tendsto.comp (Complex.continuous_ofReal.tendsto a)).mono_left nhdsWithin_le_nhds
    rw [sub_self, Complex.ofReal_zero, zero_mul, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hta : (t : ℂ) - a ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact_mod_cast (sub_pos.2 ht).ne'
    rw [hagree (show a < ((t : ℂ)).re by simpa using ht)]
    push_cast
    field_simp
  -- the residue limit at the zero
  have hres := GaloisForLFunctions.HTGeometry.tendsto_sub_mul_logDeriv_of_analyticOrderAt
    (xi_differentiable.analyticAt ρ₀) hm
  have hζ : Tendsto (fun t : ℝ => (σ : ℂ) + 2 * ((t : ℂ) + τ * I)) (𝓝[>] a) (𝓝[≠] ρ₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous fun t : ℝ => (σ : ℂ) + 2 * ((t : ℂ) + τ * I) := by fun_prop
      have h0 : (σ : ℂ) + 2 * ((a : ℂ) + τ * I) = ρ₀ := by rw [← hw₀eq, hw₀]; ring
      have := hcont.tendsto a
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro heq
      have h0 : (σ : ℂ) + 2 * ((a : ℂ) + τ * I) = ρ₀ := by rw [← hw₀eq, hw₀]; ring
      rw [← h0] at heq
      have := congrArg Complex.re heq
      simp at this
      have ht' : a < t := ht
      linarith
  have hw : Tendsto (fun t : ℝ => (t : ℂ) + τ * I) (𝓝[>] a) (𝓝 w₀) := by
    rw [hw₀eq]
    exact ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) + τ * I).tendsto a).mono_left
      nhdsWithin_le_nhds
  have hΞ : Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ) *
      logDeriv xi ((σ : ℂ) + 2 * ((t : ℂ) + τ * I))) (𝓝[>] a) (𝓝 ((m : ℂ) / 2)) := by
    have h1 := (hres.comp hζ).div_const 2
    refine h1.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp]
    have h0 : (σ : ℂ) + 2 * ((a : ℂ) + τ * I) = ρ₀ := by rw [← hw₀eq, hw₀]; ring
    rw [← h0]
    push_cast
    ring
  -- the regular part `−ηΓA + ηT + L_N` is continuous at `w₀`
  set Q : ℂ → ℂ := fun w => -(η * (Complex.Gamma w * gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
      T w)) + complexLaplace νN w with hQ
  have hw₀re : 0 < w₀.re := by rw [hw₀eq]; simpa using ha
  have hQc : ContinuousAt Q w₀ := by
    have hre : 0 < ((σ : ℂ) + 2 * w₀).re := by simp; linarith
    have hΓ : DifferentiableAt ℂ Complex.Gamma w₀ := Complex.differentiableAt_Gamma w₀
      (fun k h => by
        have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hA : DifferentiableAt ℂ (fun w : ℂ => gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w)) w₀ :=
      (differentiableAt_gaussianArchimedeanCurrent hre).comp (f := fun w : ℂ => (σ : ℂ) + 2 * w) w₀
        (by fun_prop)
    have hN' : DifferentiableAt ℂ (complexLaplace νN) w₀ :=
      hLN.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw₀re)
    exact ((((differentiableAt_const _).mul ((hΓ.mul hA).sub (hTd w₀))).neg).add hN').continuousAt
  have hΓc : ContinuousAt Complex.Gamma w₀ :=
    (Complex.differentiableAt_Gamma w₀ (fun k h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).continuousAt
  have hlimI : Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ) * complexLaplace νP ((t : ℂ) + τ * I))
      (𝓝[>] a) (𝓝 ((η : ℂ) * Complex.Gamma w₀ * ((m : ℂ) / 2))) := by
    have hta : Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ)) (𝓝[>] a) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => ((t - a : ℝ) : ℂ) := by fun_prop
      have := hc.tendsto a
      simp only [sub_self, Complex.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hden : Tendsto (fun t : ℝ => (B' : ℂ) / ((t : ℂ) + τ * I - a)) (𝓝[>] a)
        (𝓝 ((B' : ℂ) / (τ * I))) := by
      refine tendsto_const_nhds.div ?_ ?_
      · have := ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) + τ * I - a).tendsto a)
        simp only [add_sub_cancel_left] at this
        convert this.mono_left nhdsWithin_le_nhds using 2
      · exact mul_ne_zero (by exact_mod_cast hτ0) I_ne_zero
    have h1 := (hta.mul hden).add ((hta.mul (hQc.tendsto.comp hw)).add
      ((tendsto_const_nhds (x := (η : ℂ))).mul ((hΓc.tendsto.comp hw).mul hΞ)))
    rw [zero_mul, zero_mul, zero_add, zero_add, ← mul_assoc] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : a < t := ht
    rw [hagree (show a < ((t : ℂ) + τ * I).re by simpa using ht')]
    simp only [Function.comp, hR, hQ]
    ring
  -- compare the limits
  have hineq : ∀ᶠ t in 𝓝[>] a, ‖((t - a : ℝ) : ℂ) * complexLaplace νP ((t : ℂ) + τ * I)‖ ≤
      (((t - a : ℝ) : ℂ) * complexLaplace νP (t : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : a < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.2 ht'),
      complexLaplace_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (hpos t ht') (sub_pos.2 ht').le
  have hle := le_of_tendsto_of_tendsto hlimI.norm (Complex.continuous_re.tendsto _ |>.comp hlimR)
    hineq
  simp only [Complex.ofReal_re] at hle
  have hnorm : ‖(η : ℂ) * Complex.Gamma w₀ * ((m : ℂ) / 2)‖ = (m : ℝ) * ‖Complex.Gamma w₀‖ / 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_natCast,
      Complex.norm_two]
    rcases hη with h | h <;> simp [h] <;> ring
  rw [hnorm] at hle
  simpa [hw₀] using hle

private theorem exists_order_of_xi_eq_zero {ρ₀ : ℂ} (hρ₀ : xi ρ₀ = 0) :
    ∃ m : ℕ, analyticOrderAt xi ρ₀ = m ∧ 1 ≤ m := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (xi_order_ne_top ρ₀)
  refine ⟨m, hm.symm, Nat.one_le_iff_ne_zero.2 fun h0 => ?_⟩
  rw [h0] at hm
  exact (analyticOrderAt_ne_zero.2 ⟨xi_differentiable.analyticAt ρ₀, hρ₀⟩) (by rw [← hm]; rfl)

/-- **Explicit-constant Ω±.**  For `0 < σ < ½`, a zero `ρ₀` of `ξ` on the critical line, `η = ±1`
and `c < |Γ((ρ₀ − σ)/2)|/2`, the signed gap `η(P_σ − C_σ)` exceeds `c y^{-(½−σ)/2} + K` somewhere on
`(0, 1]`, for every `K`. -/
theorem exists_gaussianWeightedGap_gt_gamma {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 1 / 2) {η : ℝ}
    (hη : η = 1 ∨ η = -1) {ρ₀ : ℂ} (hρ₀ : xi ρ₀ = 0) (hρ₀re : ρ₀.re = 1 / 2) {c : ℝ}
    (hc : c < ‖Complex.Gamma ((ρ₀ - σ) / 2)‖ / 2) (K : ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧ c * y ^ (-(1 / 2 - σ) / 2) + K <
      η * (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) := by
  by_contra h
  push Not at h
  obtain ⟨m, hm, hm1⟩ := exists_order_of_xi_eq_zero hρ₀
  have hle := order_mul_norm_gamma_le_of_gaussianWeightedGap_le hσ hσ2 hη hρ₀ hρ₀re hm h
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hG := norm_nonneg (Complex.Gamma ((ρ₀ - σ) / 2))
  nlinarith

/-- **Unconditional explicit Ω±.**  For `0 < σ < ½` there is a constant `c₀ > 0` (half the size of
`Γ` at the image of a critical-line zero) such that `P_σ − C_σ` exceeds `c y^{-(½−σ)/2} + K` and falls
below `−(c y^{-(½−σ)/2} + K)` on `(0, 1]` for every `c < c₀` and every `K`. -/
theorem exists_pos_gaussianWeightedGap_omega {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 1 / 2) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c < c₀ → ∀ K : ℝ,
      (∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧ c * y ^ (-(1 / 2 - σ) / 2) + K <
        gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ∧
      (∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧
        gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y <
          -(c * y ^ (-(1 / 2 - σ) / 2) + K)) := by
  obtain ⟨ρ₀, hρ₀, hρ₀re⟩ := exists_xi_zero_re_eq_half
  refine ⟨‖Complex.Gamma ((ρ₀ - σ) / 2)‖ / 2, ?_, fun c hc K => ⟨?_, ?_⟩⟩
  · have hre : 0 < ((ρ₀ - σ) / 2).re := by simp [hρ₀re]; linarith
    have := Complex.Gamma_ne_zero_of_re_pos hre
    have := norm_pos_iff.2 this
    positivity
  · obtain ⟨y, hy, hy1, h⟩ := exists_gaussianWeightedGap_gt_gamma hσ hσ2 (Or.inl rfl) hρ₀ hρ₀re hc K
    exact ⟨y, hy, hy1, by linarith⟩
  · obtain ⟨y, hy, hy1, h⟩ := exists_gaussianWeightedGap_gt_gamma hσ hσ2 (Or.inr rfl) hρ₀ hρ₀re hc K
    exact ⟨y, hy, hy1, by linarith⟩

end

end RHTower
