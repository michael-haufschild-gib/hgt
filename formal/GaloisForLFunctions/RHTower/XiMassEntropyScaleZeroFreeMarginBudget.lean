import GaloisForLFunctions.RHTower.XiMassFiniteOrderZeroFreeMarginBudget

/-!
# Xi zero-free margin budget near entropy scale

A residual fraction `log(3A+9)^(11 : ℕ)/A` is smaller than every fixed algebraic margin order but
still yields logarithmic-square decay against linear-log corona entropy.  The complete literal
source vanishes, locating the remaining constant-sensitive boundary at order `log(A)^(10 : ℕ)/A`.
-/

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Residual budget one logarithm above entropy-critical scale. -/
def xiMassEntropyResidualFraction (A : ℝ) : ℝ :=
  Real.log (3 * A + 9) ^ (11 : ℕ) / A

/-- Near-entropy residual fraction still tends to zero. -/
theorem tendsto_xiMassEntropyResidualFraction_zero :
    Tendsto xiMassEntropyResidualFraction atTop (𝓝 0) := by
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hraw := (tendsto_pow_log_two_mul_add_nine_div_id 11).comp hscale
  have hmul : Tendsto (fun A : ℝ => (3 / 2 : ℝ) *
      (Real.log (2 * ((3 / 2) * A) + 9) ^ (11 : ℕ) / ((3 / 2) * A)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      Filter.Tendsto.const_mul (3 / 2 : ℝ) hraw
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  unfold xiMassEntropyResidualFraction
  rw [show 2 * ((3 / 2 : ℝ) * A) + 9 = 3 * A + 9 by ring]
  field_simp

/-- Logarithmic-square envelope after rescaling B=3A/2. -/
def xiMassEntropyScaledEnvelope (σ B : ℝ) : ℝ :=
  xiZeroCountEnvelopeConstant * (2 * B + 3) * Real.log (2 * B + 4) *
    Real.exp (-(3 * σ * xiWardZeroFreeMarginC / 13) *
      Real.log (2 * B + 9) ^ (2 : ℕ))

/-- One logarithm above entropy scale gives unconditional widened-corona extinction. -/
theorem tendsto_xiMassEntropyScaledEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassEntropyScaledEnvelope σ) atTop (𝓝 0) := by
  let C : ℝ := xiZeroCountEnvelopeConstant
  let D : ℝ := C + 1
  let c : ℝ := 3 * σ * xiWardZeroFreeMarginC / 13
  have hC : 0 < C := by dsimp only [C]; exact xiZeroCountEnvelopeConstant_pos
  have hD : 0 < D := by dsimp only [D]; linarith
  have hD1 : 1 < D := by dsimp only [D]; linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos (mul_pos (by norm_num) hσ) xiWardZeroFreeMarginC_pos)
      (by norm_num)
  have haff : Tendsto (fun B : ℝ => 2 * B + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hLtop : Tendsto (fun B : ℝ => Real.log (2 * B + 9)) atTop atTop :=
    Real.tendsto_log_atTop.comp haff
  have hlarge : ∀ᶠ B : ℝ in atTop,
      1 ≤ Real.log (2 * B + 9) ∧
      8 / c ≤ Real.log (2 * B + 9) ∧
      4 * Real.log D / c ≤ Real.log (2 * B + 9) := by
    filter_upwards [hLtop.eventually_ge_atTop 1,
      hLtop.eventually_ge_atTop (8 / c),
      hLtop.eventually_ge_atTop (4 * Real.log D / c)] with B h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hbudget : ∀ᶠ B : ℝ in atTop,
      Real.log D + 2 * Real.log (2 * B + 9) ≤
        c / 2 * Real.log (2 * B + 9) ^ (2 : ℕ) := by
    filter_upwards [hlarge] with B hlargeB
    let L : ℝ := Real.log (2 * B + 9)
    have hL1 : 1 ≤ L := by simpa only [L] using hlargeB.1
    have hL8 : 8 / c ≤ L := by simpa only [L] using hlargeB.2.1
    have hLD : 4 * Real.log D / c ≤ L := by simpa only [L] using hlargeB.2.2
    have hpart1 : Real.log D ≤ c / 4 * L ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_left hLD (show 0 ≤ c / 4 * L by positivity)
      calc
        Real.log D ≤ L * Real.log D := by nlinarith [hL1, hlogD]
        _ = (c / 4 * L) * (4 * Real.log D / c) := by
          field_simp [hc.ne']
        _ ≤ (c / 4 * L) * L := hmul
        _ = c / 4 * L ^ (2 : ℕ) := by ring
    have hpart2 : 2 * L ≤ c / 4 * L ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_left hL8 (show 0 ≤ c / 4 * L by positivity)
      calc
        2 * L = (c / 4 * L) * (8 / c) := by
          field_simp [hc.ne']
          ring
        _ ≤ (c / 4 * L) * L := hmul
        _ = c / 4 * L ^ (2 : ℕ) := by ring
    dsimp only [L] at hpart1 hpart2 ⊢
    linarith
  have hLsq : Tendsto (fun B : ℝ => Real.log (2 * B + 9) ^ (2 : ℕ))
      atTop atTop := (Filter.tendsto_pow_atTop (by norm_num)).comp hLtop
  have hscaledBot : Tendsto (fun B : ℝ => -(c / 2) *
      Real.log (2 * B + 9) ^ (2 : ℕ)) atTop atBot :=
    hLsq.const_mul_atTop_of_neg (by linarith)
  have hdecay : Tendsto (fun B : ℝ => Real.exp (-(c / 2) *
      Real.log (2 * B + 9) ^ (2 : ℕ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hscaledBot
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    unfold xiMassEntropyScaledEnvelope
    have hlog : 0 ≤ Real.log (2 * B + 4) := Real.log_nonneg (by linarith)
    change 0 ≤ C * (2 * B + 3) * Real.log (2 * B + 4) *
      Real.exp (-c * Real.log (2 * B + 9) ^ (2 : ℕ))
    positivity
  · filter_upwards [hbudget, eventually_gt_atTop (0 : ℝ)] with B hbudgetB hB
    let x : ℝ := 2 * B + 9
    let y : ℝ := 2 * B + 4
    let L : ℝ := Real.log x
    let P : ℝ := C * (2 * B + 3) * Real.log y
    have hx : 0 < x := by dsimp only [x]; linarith
    have hy : 0 < y := by dsimp only [y]; linarith
    have hL : 0 < L := by dsimp only [L]; exact Real.log_pos (by dsimp only [x]; linarith)
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
    have hP : P ≤ D * x ^ (2 : ℕ) := by
      dsimp only [P]
      calc
        C * (2 * B + 3) * Real.log y ≤ D * x * x := by gcongr
        _ = D * x ^ (2 : ℕ) := by ring
    have hexpEq : Real.exp (Real.log D + 2 * L) = D * x ^ (2 : ℕ) := by
      rw [Real.exp_add, Real.exp_log hD]
      have htwo : 2 * L = L + L := by ring
      rw [htwo, Real.exp_add]
      dsimp only [L]
      rw [Real.exp_log hx]
      ring
    have hPexp : P ≤ Real.exp (c / 2 * L ^ (2 : ℕ)) := by
      calc
        P ≤ D * x ^ (2 : ℕ) := hP
        _ = Real.exp (Real.log D + 2 * L) := hexpEq.symm
        _ ≤ Real.exp (c / 2 * L ^ (2 : ℕ)) := by
          apply Real.exp_le_exp.mpr
          simpa only [L, x] using hbudgetB
    have hcalc : P * Real.exp (-c * L ^ (2 : ℕ)) ≤ Real.exp (-(c / 2) * L ^ (2 : ℕ)) := by
      calc
        P * Real.exp (-c * L ^ (2 : ℕ)) ≤ Real.exp (c / 2 * L ^ (2 : ℕ)) * Real.exp (-c * L ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hPexp (Real.exp_pos _).le
        _ = Real.exp (-(c / 2) * L ^ (2 : ℕ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    change P * Real.exp (-c * L ^ (2 : ℕ)) ≤ Real.exp (-(c / 2) * L ^ (2 : ℕ))
    exact hcalc
  · exact hdecay

/-- Spent fraction for the near-entropy schedule. -/
def xiMassEntropyBudgetFraction (A : ℝ) : ℝ :=
  1 - xiMassEntropyResidualFraction A

theorem eventually_xiMassEntropyBudgetFraction_pos_lt_one :
    ∀ᶠ A : ℝ in atTop,
      0 < xiMassEntropyBudgetFraction A ∧ xiMassEntropyBudgetFraction A < 1 := by
  have hsmall := tendsto_xiMassEntropyResidualFraction_zero.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with A hsmallA hA
  have hx : 1 < 3 * A + 9 := by linarith
  have hL : 0 < Real.log (3 * A + 9) := Real.log_pos hx
  have hres : 0 < xiMassEntropyResidualFraction A := by
    unfold xiMassEntropyResidualFraction
    exact div_pos (pow_pos hL 11) hA
  unfold xiMassEntropyBudgetFraction
  constructor <;> linarith

theorem tendsto_xiMassEntropyBudgetFraction_one :
    Tendsto xiMassEntropyBudgetFraction atTop (𝓝 1) := by
  unfold xiMassEntropyBudgetFraction
  simpa only [sub_zero] using
    tendsto_const_nhds.sub tendsto_xiMassEntropyResidualFraction_zero

/-- Near-entropy corona envelope before aperture rescaling. -/
def xiMassEntropyBudgetEnvelope (σ A : ℝ) : ℝ :=
  xiMassMarginBudgetEnvelope σ (xiMassEntropyBudgetFraction A) A

theorem xiMassEntropyBudgetEnvelope_eq_scaled
    (σ : ℝ) {A : ℝ} (hA : 0 < A) :
    xiMassEntropyBudgetEnvelope σ A =
      xiMassEntropyScaledEnvelope σ ((3 / 2) * A) := by
  have hL : 0 < Real.log (3 * A + 9) := Real.log_pos (by linarith)
  unfold xiMassEntropyBudgetEnvelope xiMassEntropyBudgetFraction
    xiMassEntropyResidualFraction xiMassMarginBudgetEnvelope
    xiMassCriticalZeroFreeEnvelope xiMassEntropyScaledEnvelope
  rw [show 2 * ((3 / 2 : ℝ) * A) = 3 * A by ring]
  unfold xiWardZeroFreeMargin
  rw [abs_of_nonneg (by positivity : 0 ≤ 3 * A)]
  congr 2
  field_simp [hA.ne', hL.ne']
  ring

theorem tendsto_xiMassEntropyBudgetEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassEntropyBudgetEnvelope σ) atTop (𝓝 0) := by
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have h := (tendsto_xiMassEntropyScaledEnvelope_zero hσ).comp hscale
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  exact (xiMassEntropyBudgetEnvelope_eq_scaled σ hA).symm

/-- Explicit frequency one logarithm above entropy-critical residual scale. -/
def xiMassEntropyBudgetFrequency (σ A : ℝ) : ℝ :=
  xiMassMarginBudgetFrequency σ (xiMassEntropyBudgetFraction A) A

theorem xiMassEntropyBudgetFrequency_pos
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ1 : xiMassEntropyBudgetFraction A < 1) :
    0 < xiMassEntropyBudgetFrequency σ A := by
  unfold xiMassEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_pos hσ hθ1.le hA

theorem xiMassEntropyBudgetFrequency_layer_eq
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ1 : xiMassEntropyBudgetFraction A < 1) :
    |xiMassEntropyBudgetFrequency σ A| *
        (1 / 2 - xiMassEntropyBudgetFraction A *
          xiWardZeroFreeMargin (3 * A)) = 2 * σ * A := by
  unfold xiMassEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_layer_eq hσ hθ1.le hA

theorem xiMassEntropyBudgetFrequency_lower
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ0 : 0 < xiMassEntropyBudgetFraction A)
    (hθ1 : xiMassEntropyBudgetFraction A < 1) :
    2 * σ * A ≤ |xiMassEntropyBudgetFrequency σ A| := by
  unfold xiMassEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_lower hσ hθ0 hθ1 hA

theorem xiMassEntropyBudgetFrequency_strictly_subcritical
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ0 : 0 < xiMassEntropyBudgetFraction A)
    (hθ1 : xiMassEntropyBudgetFraction A < 1) :
    4 * σ * A < |xiMassEntropyBudgetFrequency σ A| := by
  unfold xiMassEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_strictly_subcritical hσ hθ0 hθ1 hA

theorem tendsto_xiMassEntropyBudgetFrequency_atTop
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassEntropyBudgetFrequency σ) atTop atTop := by
  have hlinear : Tendsto (fun A : ℝ => 4 * σ * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_xiMassEntropyBudgetFraction_pos_lt_one,
    eventually_gt_atTop (0 : ℝ)] with A hθ hA
  have huPos := xiMassEntropyBudgetFrequency_pos hσ hA hθ.2
  simpa only [abs_of_pos huPos] using
    (xiMassEntropyBudgetFrequency_strictly_subcritical hσ hA hθ.1 hθ.2).le

/-- **Near-entropy extinction.**  One logarithm above entropy-critical residual scale, the
complete literal source still vanishes on an explicit genuinely subcritical schedule. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_entropyBudget_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun A : ℝ =>
      ‖xiMassBottomPrimeIntegral (A + 1 / 2) 1
        ((σ : ℂ) + xiMassEntropyBudgetFrequency σ A * I)‖)
      atTop (𝓝 0) := by
  have henv := tendsto_xiMassEntropyBudgetEnvelope_zero hσ
  have henvMul : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassEntropyBudgetEnvelope σ A)
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
      ‖(Real.pi : ℂ) * I‖ * xiMassEntropyBudgetEnvelope σ A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ),
      eventually_xiMassEntropyBudgetFraction_pos_lt_one] with A hA hθ
    have hApos : 0 < A := by linarith
    let θ : ℝ := xiMassEntropyBudgetFraction A
    have hlower := xiMassEntropyBudgetFrequency_lower hσ hApos hθ.1 hθ.2
    have hlayer := (xiMassEntropyBudgetFrequency_layer_eq hσ hApos hθ.2).le
    have hbound := norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope
      (a := A + 1 / 2) (σ := σ) (θ := θ)
      (u := xiMassEntropyBudgetFrequency σ A) (by linarith) hσ hθ.2
      (by simpa only [add_sub_cancel_right] using hlower)
      (by simpa only [add_sub_cancel_right, θ] using hlayer)
    simpa only [add_sub_cancel_right, xiMassEntropyBudgetEnvelope, θ] using hbound
  · exact hmajor

end

end RHTower

