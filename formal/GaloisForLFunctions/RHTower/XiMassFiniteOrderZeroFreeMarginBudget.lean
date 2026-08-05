import GaloisForLFunctions.RHTower.XiMassSecondOrderZeroFreeMarginBudget

/-!
# All finite-order Xi zero-free margin budgets

For every fixed positive natural order `N`, the spent fraction approaches one as
`1 - d_A^N`, leaving residual width `d_A^(N+1)`.  Its mass scale still defeats exact
widened-corona entropy, proving unconditional literal-source extinction at every finite order.
-/

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Widened-corona envelope with residual zero-free width of arbitrary finite order. -/
def xiMassFiniteOrderScaledEnvelope (σ : ℝ) (N : ℕ) (B : ℝ) : ℝ :=
  xiZeroCountEnvelopeConstant * (2 * B + 3) * Real.log (2 * B + 4) *
    Real.exp (-(2 * σ / 13) * B * xiWardZeroFreeMargin (2 * B) ^ (N + 1))

/-- Every finite algebraic residual-margin order absorbs widened-corona entropy. -/
theorem tendsto_xiMassFiniteOrderScaledEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    Tendsto (xiMassFiniteOrderScaledEnvelope σ N) atTop (𝓝 0) := by
  let C : ℝ := xiZeroCountEnvelopeConstant
  let D : ℝ := C + 1
  let n : ℕ := 9 * (N + 1)
  let c : ℝ := (2 * σ / 13) * xiWardZeroFreeMarginC ^ (N + 1)
  have hC : 0 < C := by dsimp only [C]; exact xiZeroCountEnvelopeConstant_pos
  have hD : 0 < D := by dsimp only [D]; linarith
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (by positivity) (pow_pos xiWardZeroFreeMarginC_pos (N + 1))
  have hn := tendsto_pow_log_two_mul_add_nine_div_id n
  have hn1 := tendsto_pow_log_two_mul_add_nine_div_id (n + 1)
  have hcombo :
      Tendsto (fun B : ℝ =>
        Real.log D * (Real.log (2 * B + 9) ^ n / B) +
          2 * (Real.log (2 * B + 9) ^ (n + 1) / B))
        atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      (tendsto_const_nhds.mul hn).add (tendsto_const_nhds.mul hn1)
  have hsmall := hcombo.eventually_le_const (show 0 < c / 2 by positivity)
  have hscale := tendsto_xiZeroFreeScale_pow n
  have hscaledBot :
      Tendsto (fun B : ℝ => -(c / 2) *
        (B / Real.log (2 * B + 9) ^ n)) atTop atBot :=
    hscale.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (div_pos hc (by norm_num)))
  have hdecay :
      Tendsto (fun B : ℝ =>
        Real.exp (-(c / 2) * (B / Real.log (2 * B + 9) ^ n)))
        atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp hscaledBot
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    unfold xiMassFiniteOrderScaledEnvelope
    have hlog : 0 ≤ Real.log (2 * B + 4) := Real.log_nonneg (by linarith)
    change 0 ≤ C * (2 * B + 3) * Real.log (2 * B + 4) *
      Real.exp (-(2 * σ / 13) * B * xiWardZeroFreeMargin (2 * B) ^ (N + 1))
    positivity
  · filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with B hsmallB hB
    let x : ℝ := 2 * B + 9
    let y : ℝ := 2 * B + 4
    let L : ℝ := Real.log x
    let X : ℝ := B / L ^ n
    let P : ℝ := C * (2 * B + 3) * Real.log y
    have hx : 0 < x := by dsimp only [x]; linarith
    have hy : 0 < y := by dsimp only [y]; linarith
    have hL : 0 < L := by
      dsimp only [L]
      exact Real.log_pos (by dsimp only [x]; linarith)
    have hLn : 0 < L ^ n := pow_pos hL n
    have hCD : C ≤ D := by dsimp only [D]; linarith
    have hfac0 : 0 ≤ 2 * B + 3 := by linarith
    have hfac : 2 * B + 3 ≤ x := by dsimp only [x]; linarith
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by dsimp only [y]; linarith)
    have hlogyx : Real.log y ≤ L := by
      dsimp only [L]
      exact Real.log_le_log hy (by dsimp only [x, y]; linarith)
    have hLx : L ≤ x := by
      have h := Real.log_le_sub_one_of_pos hx
      dsimp only [L]
      linarith
    have hlogyx' : Real.log y ≤ x := hlogyx.trans hLx
    have hP : P ≤ D * x ^ 2 := by
      dsimp only [P]
      calc
        C * (2 * B + 3) * Real.log y ≤ D * x * x := by gcongr
        _ = D * x ^ 2 := by ring
    have hsmallMul :
        Real.log D * L ^ n + 2 * L ^ (n + 1) ≤ c / 2 * B := by
      have hmul := mul_le_mul_of_nonneg_left hsmallB hB.le
      have heqLeft :
          B * (Real.log D * (L ^ n / B) + 2 * (L ^ (n + 1) / B)) =
            Real.log D * L ^ n + 2 * L ^ (n + 1) := by
        field_simp
      rw [show Real.log (2 * B + 9) = L by rfl, heqLeft] at hmul
      nlinarith
    have hbudget : Real.log D + 2 * L ≤ c / 2 * X := by
      dsimp only [X]
      rw [show c / 2 * (B / L ^ n) = (c / 2 * B) / L ^ n by ring,
        le_div_iff₀ hLn]
      calc
        (Real.log D + 2 * L) * L ^ n =
            Real.log D * L ^ n + 2 * L ^ (n + 1) := by ring
        _ ≤ c / 2 * B := hsmallMul
    have hexpEq : Real.exp (Real.log D + 2 * L) = D * x ^ 2 := by
      rw [Real.exp_add, Real.exp_log hD]
      have htwo : 2 * L = L + L := by ring
      rw [htwo, Real.exp_add]
      dsimp only [L]
      rw [Real.exp_log hx]
      ring
    have hPexp : P ≤ Real.exp (c / 2 * X) := by
      calc
        P ≤ D * x ^ 2 := hP
        _ = Real.exp (Real.log D + 2 * L) := hexpEq.symm
        _ ≤ Real.exp (c / 2 * X) := Real.exp_le_exp.mpr hbudget
    have hcalc : P * Real.exp (-c * X) ≤ Real.exp (-(c / 2) * X) := by
      calc
        P * Real.exp (-c * X) ≤ Real.exp (c / 2 * X) * Real.exp (-c * X) :=
          mul_le_mul_of_nonneg_right hPexp (Real.exp_pos _).le
        _ = Real.exp (-(c / 2) * X) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hmargin :
        xiWardZeroFreeMargin (2 * B) = xiWardZeroFreeMarginC / L ^ (9 : ℕ) := by
      unfold xiWardZeroFreeMargin
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * B)]
    have hexponent :
        -(2 * σ / 13) * B *
            (xiWardZeroFreeMarginC / L ^ (9 : ℕ)) ^ (N + 1) = -c * X := by
      rw [div_pow, ← pow_mul]
      dsimp only [c, X, n]
      ring
    change P * Real.exp (-(2 * σ / 13) * B *
      xiWardZeroFreeMargin (2 * B) ^ (N + 1)) ≤ Real.exp (-(c / 2) * X)
    rw [hmargin, hexponent]
    exact hcalc
  · exact hdecay

/-- Spend all but the `N`th power of known zero-free width. -/
def xiMassFiniteOrderBudgetFraction (N : ℕ) (A : ℝ) : ℝ :=
  1 - xiWardZeroFreeMargin (3 * A) ^ N

theorem xiMassFiniteOrderBudgetFraction_pos
    {N : ℕ} (hN : 0 < N) (A : ℝ) :
    0 < xiMassFiniteOrderBudgetFraction N A := by
  unfold xiMassFiniteOrderBudgetFraction
  have hd0 := (xiWardZeroFreeMargin_pos (3 * A)).le
  have hdlt : xiWardZeroFreeMargin (3 * A) < 1 := by
    have hd8 := xiWardZeroFreeMargin_le_one_eighth (3 * A)
    linarith
  have hpow := pow_lt_one₀ hd0 hdlt (Nat.ne_of_gt hN)
  linarith

theorem xiMassFiniteOrderBudgetFraction_lt_one
    (N : ℕ) (A : ℝ) :
    xiMassFiniteOrderBudgetFraction N A < 1 := by
  unfold xiMassFiniteOrderBudgetFraction
  have hpow : 0 < xiWardZeroFreeMargin (3 * A) ^ N :=
    pow_pos (xiWardZeroFreeMargin_pos _) N
  linarith

theorem tendsto_xiMassFiniteOrderBudgetFraction_one
    {N : ℕ} (hN : 0 < N) :
    Tendsto (xiMassFiniteOrderBudgetFraction N) atTop (𝓝 1) := by
  have hpow := tendsto_xiWardZeroFreeMargin_three_mul_zero.pow N
  have hpow0 : Tendsto (fun A : ℝ => xiWardZeroFreeMargin (3 * A) ^ N)
      atTop (𝓝 0) := by
    simpa only [zero_pow (Nat.ne_of_gt hN)] using hpow
  unfold xiMassFiniteOrderBudgetFraction
  simpa only [sub_zero] using tendsto_const_nhds.sub hpow0

/-- Moving finite-order budget envelope before aperture rescaling. -/
def xiMassFiniteOrderBudgetEnvelope (σ : ℝ) (N : ℕ) (A : ℝ) : ℝ :=
  xiMassMarginBudgetEnvelope σ (xiMassFiniteOrderBudgetFraction N A) A

theorem xiMassFiniteOrderBudgetEnvelope_eq_scaled (σ : ℝ) (N : ℕ) (A : ℝ) :
    xiMassFiniteOrderBudgetEnvelope σ N A =
      xiMassFiniteOrderScaledEnvelope σ N ((3 / 2) * A) := by
  unfold xiMassFiniteOrderBudgetEnvelope xiMassFiniteOrderBudgetFraction
    xiMassMarginBudgetEnvelope xiMassCriticalZeroFreeEnvelope
    xiMassFiniteOrderScaledEnvelope
  rw [show 2 * ((3 / 2 : ℝ) * A) = 3 * A by ring]
  congr 2
  rw [pow_succ]
  ring_nf

theorem tendsto_xiMassFiniteOrderBudgetEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    Tendsto (xiMassFiniteOrderBudgetEnvelope σ N) atTop (𝓝 0) := by
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have h := (tendsto_xiMassFiniteOrderScaledEnvelope_zero hσ N).comp hscale
  exact h.congr' (Eventually.of_forall fun A =>
    (xiMassFiniteOrderBudgetEnvelope_eq_scaled σ N A).symm)

/-- Explicit frequency at finite algebraic margin order `N`. -/
def xiMassFiniteOrderBudgetFrequency (σ : ℝ) (N : ℕ) (A : ℝ) : ℝ :=
  xiMassMarginBudgetFrequency σ (xiMassFiniteOrderBudgetFraction N A) A

theorem xiMassFiniteOrderBudgetFrequency_pos
    {σ A : ℝ} {N : ℕ} (hσ : 0 < σ) (hA : 0 < A) :
    0 < xiMassFiniteOrderBudgetFrequency σ N A := by
  unfold xiMassFiniteOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_pos hσ
    (xiMassFiniteOrderBudgetFraction_lt_one N A).le hA

theorem xiMassFiniteOrderBudgetFrequency_layer_eq
    {σ A : ℝ} {N : ℕ} (hσ : 0 < σ) (hA : 0 < A) :
    |xiMassFiniteOrderBudgetFrequency σ N A| *
        (1 / 2 - xiMassFiniteOrderBudgetFraction N A *
          xiWardZeroFreeMargin (3 * A)) = 2 * σ * A := by
  unfold xiMassFiniteOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_layer_eq hσ
    (xiMassFiniteOrderBudgetFraction_lt_one N A).le hA

theorem xiMassFiniteOrderBudgetFrequency_lower
    {σ A : ℝ} {N : ℕ} (hσ : 0 < σ) (hN : 0 < N) (hA : 0 < A) :
    2 * σ * A ≤ |xiMassFiniteOrderBudgetFrequency σ N A| := by
  unfold xiMassFiniteOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_lower hσ
    (xiMassFiniteOrderBudgetFraction_pos hN A)
    (xiMassFiniteOrderBudgetFraction_lt_one N A) hA

/-- Every finite-order schedule is genuinely below the universal geometric wall. -/
theorem xiMassFiniteOrderBudgetFrequency_strictly_subcritical
    {σ A : ℝ} {N : ℕ} (hσ : 0 < σ) (hN : 0 < N) (hA : 0 < A) :
    4 * σ * A < |xiMassFiniteOrderBudgetFrequency σ N A| := by
  unfold xiMassFiniteOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_strictly_subcritical hσ
    (xiMassFiniteOrderBudgetFraction_pos hN A)
    (xiMassFiniteOrderBudgetFraction_lt_one N A) hA

theorem tendsto_xiMassFiniteOrderBudgetFrequency_atTop
    {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) :
    Tendsto (xiMassFiniteOrderBudgetFrequency σ N) atTop atTop := by
  have hlinear : Tendsto (fun A : ℝ => 4 * σ * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  simpa only [abs_of_pos (xiMassFiniteOrderBudgetFrequency_pos hσ hA)] using
    (xiMassFiniteOrderBudgetFrequency_strictly_subcritical hσ hN hA).le

/-- **All finite-order moving-budget extinction.**  For every fixed positive natural order, the
complete literal source vanishes although the budget approaches the full zero-free edge to that
algebraic order. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_finiteOrderBudget_zero
    {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) :
    Tendsto (fun A : ℝ =>
      ‖xiMassBottomPrimeIntegral (A + 1 / 2) 1
        ((σ : ℂ) + xiMassFiniteOrderBudgetFrequency σ N A * I)‖)
      atTop (𝓝 0) := by
  have henv := tendsto_xiMassFiniteOrderBudgetEnvelope_zero hσ N
  have henvMul : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassFiniteOrderBudgetEnvelope σ N A)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ henv
  have hexpTrace : Tendsto (fun A : ℝ => Real.exp (-(σ / 12) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 12) < 0))
  have hexpArch : Tendsto (fun A : ℝ => Real.exp (-(σ / 2) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 2) < 0))
  have htraceTail : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ *
        (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)))
      atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.mul_const (xiPoissonTraceReal (σ / 12)) hexpTrace
    have h2 := Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ h1
    simpa only [zero_mul, mul_zero] using h2
  have harchTail : Tendsto (fun A : ℝ =>
      Real.exp (-(σ / 2) * A) * xiMassBottomArchUniformBound 2 (σ / 2))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      Filter.Tendsto.mul_const (xiMassBottomArchUniformBound 2 (σ / 2)) hexpArch
  have hmajor : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassFiniteOrderBudgetEnvelope σ N A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with A hA
    have hApos : 0 < A := by linarith
    let θ : ℝ := xiMassFiniteOrderBudgetFraction N A
    have hθ1 : θ < 1 := xiMassFiniteOrderBudgetFraction_lt_one N A
    have hlower := xiMassFiniteOrderBudgetFrequency_lower hσ hN hApos
    have hlayer :=
      (xiMassFiniteOrderBudgetFrequency_layer_eq (N := N) hσ hApos).le
    have hbound := norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope
      (a := A + 1 / 2) (σ := σ) (θ := θ)
      (u := xiMassFiniteOrderBudgetFrequency σ N A) (by linarith) hσ hθ1
      (by simpa only [add_sub_cancel_right] using hlower)
      (by simpa only [add_sub_cancel_right, θ] using hlayer)
    simpa only [add_sub_cancel_right, xiMassFiniteOrderBudgetEnvelope, θ] using hbound
  · exact hmajor

end

end RHTower

