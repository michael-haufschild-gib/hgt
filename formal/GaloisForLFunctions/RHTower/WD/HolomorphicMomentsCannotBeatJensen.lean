import Mathlib.Analysis.Complex.MeanValue

/-!
# Holomorphic moments and the mean square cannot beat Jensen

Let `f` be a mollified product `ζM` on the line `Re s = ½ + b/log T`, sampled at a uniform height
`t ∈ [T, 2T]`. Its unconditional mean-value data are the holomorphic moments `E f^k = 1` (for `k`
below the length cap) and the mean square `E|f|² = c`. Littlewood's lemma turns `E log|f|` into
the off-line first moment, and Jensen bounds it by `½ log c`. This module shows that the bound is
sharp for these data.

* **Jensen ceiling** (`integral_log_norm_le_half_log_integral_sq`): for every probability law of a
  nowhere-vanishing `g`, `∫ log‖g‖ ≤ ½ log ∫ ‖g‖²`.
* **Extremal law** (`jensenExtremal`): the boundary values of the disc automorphism
  `F(w) = r⁻¹ (w + r)/(1 + r w)`, `0 < r < 1`, have every holomorphic moment equal to `1`
  (mean value property, `F(0) = 1`) and constant modulus `r⁻¹` on the unit circle.
* **Sharpness** (`exists_jensen_extremal`): for every `c > 1` some `F` holomorphic on a
  neighbourhood of the closed disc has `circleAverage F^k = 1` for all `k`, mean square `c` and
  log-mean exactly `½ log c`.

So any bound on the log-mean that uses only holomorphic moments and the mean square is at least
`½ log c`; a mollifier of fixed length leaves `c > 1`, and the loss is the log-variance of `f`, not a
defect of the argument.
-/

open Complex Metric Real MeasureTheory

namespace GaloisForLFunctions.RHTower.WD

noncomputable section

/-! ## The Jensen ceiling -/

/-- **Jensen's inequality for `log`.** For a probability measure and a nowhere-vanishing `g` with
square-integrable modulus, `∫ log‖g‖ ≤ ½ log ∫ ‖g‖²`. The proof integrates
`log y ≤ y − 1` at `y = ‖g‖²/m`, `m = ∫ ‖g‖²`. -/
theorem integral_log_norm_le_half_log_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℂ}
    (hg0 : ∀ᵐ x ∂μ, g x ≠ 0)
    (hsq : Integrable (fun x => ‖g x‖ ^ 2) μ)
    (hlog : Integrable (fun x => Real.log ‖g x‖) μ) :
    ∫ x, Real.log ‖g x‖ ∂μ ≤ Real.log (∫ x, ‖g x‖ ^ 2 ∂μ) / 2 := by
  set m := ∫ x, ‖g x‖ ^ 2 ∂μ with hm_def
  have hpos_ae : ∀ᵐ x ∂μ, 0 < ‖g x‖ ^ 2 := hg0.mono fun x hx => by positivity
  have hle : (0 : α → ℝ) ≤ᵐ[μ] fun x => ‖g x‖ ^ 2 :=
    Filter.Eventually.of_forall fun x => by positivity
  have hm : 0 < m := by
    rcases (integral_nonneg_of_ae hle).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := (integral_eq_zero_iff_of_nonneg_ae hle hsq).mp h.symm
      have hF : ∀ᵐ _x ∂μ, False := by
        filter_upwards [h0, hpos_ae] with x h1 h2
        exact h2.ne' h1
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hF
      exact IsProbabilityMeasure.ne_zero μ hF
  -- Pointwise: `2 log‖g‖ − log m ≤ ‖g‖²/m − 1`.
  have hpt : ∀ᵐ x ∂μ, 2 * Real.log ‖g x‖ - Real.log m ≤ ‖g x‖ ^ 2 / m - 1 := by
    filter_upwards [hpos_ae] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx hm)
    rwa [Real.log_div hx.ne' hm.ne', Real.log_pow, Nat.cast_ofNat] at h
  have hint_l : Integrable (fun x => 2 * Real.log ‖g x‖ - Real.log m) μ :=
    (hlog.const_mul 2).sub (integrable_const _)
  have hint_r : Integrable (fun x => ‖g x‖ ^ 2 / m - 1) μ :=
    (hsq.div_const m).sub (integrable_const _)
  have hmono := integral_mono_ae hint_l hint_r hpt
  rw [integral_sub (hlog.const_mul 2) (integrable_const _), integral_const_mul,
    integral_sub (hsq.div_const m) (integrable_const _), integral_div] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  rw [div_self hm.ne', sub_self] at hmono
  linarith

/-! ## The extremal law -/

/-- The boundary law of the disc automorphism sending `0` to `r`, rescaled by `r⁻¹`. -/
def jensenExtremal (r : ℝ) (w : ℂ) : ℂ := (r : ℂ)⁻¹ * ((w + r) / (1 + r * w))

theorem one_add_mul_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1 + (r : ℂ) * w ≠ 0 := by
  intro h
  have h1 : (r : ℂ) * w = -1 := by linear_combination h
  have h2 : r * ‖w‖ = 1 := by
    have := congrArg norm h1
    rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, norm_neg, norm_one] at this
  nlinarith [norm_nonneg w]

theorem differentiableOn_jensenExtremal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    DifferentiableOn ℂ (jensenExtremal r) (closedBall 0 1) := by
  intro w hw
  have hw' : ‖w‖ ≤ 1 := by simpa using hw
  have hden := one_add_mul_ne_zero hr0 hr1 hw'
  have h : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ)⁻¹ * ((w + r) / (1 + r * w))) w := by
    fun_prop (disch := exact hden)
  exact h.differentiableWithinAt

/-- On the unit circle `‖w + r‖ = ‖1 + r w‖`, so the extremal law has constant modulus `r⁻¹`. -/
theorem norm_jensenExtremal {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖jensenExtremal r w‖ = r⁻¹ := by
  have hden := one_add_mul_ne_zero hr0.le hr1 hw.le
  have hwc : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  have hsplit : w + r = w * (1 + r * (starRingEnd ℂ) w) := by
    linear_combination (-(r : ℂ)) * hwc
  have hconj : ‖1 + (r : ℂ) * (starRingEnd ℂ) w‖ = ‖1 + (r : ℂ) * w‖ := by
    rw [← Complex.norm_conj (1 + (r : ℂ) * w)]
    simp [map_add, map_mul, Complex.conj_ofReal]
  have hnum : ‖w + r‖ = ‖1 + (r : ℂ) * w‖ := by
    rw [hsplit, norm_mul, hw, one_mul, hconj]
  unfold jensenExtremal
  rw [norm_mul, norm_div, hnum, div_self (norm_ne_zero_iff.mpr hden), mul_one, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hr0.le]

theorem jensenExtremal_zero {r : ℝ} (hr0 : 0 < r) : jensenExtremal r 0 = 1 := by
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  unfold jensenExtremal
  field_simp
  ring

/-- Every holomorphic moment of the extremal law is `1` (mean value property). -/
theorem circleAverage_pow_jensenExtremal {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    circleAverage (fun w => jensenExtremal r w ^ k) 0 1 = 1 := by
  have hdiff : DifferentiableOn ℂ (fun w => jensenExtremal r w ^ k) (closedBall 0 1) :=
    (differentiableOn_jensenExtremal hr0.le hr1).pow k
  have hcl : DiffContOnCl ℂ (fun w => jensenExtremal r w ^ k) (ball (0 : ℂ) |1|) := by
    rw [abs_one]
    exact DifferentiableOn.diffContOnCl (by rwa [closure_ball (0 : ℂ) one_ne_zero])
  rw [hcl.circleAverage, jensenExtremal_zero hr0, one_pow]

theorem circleAverage_sq_norm_jensenExtremal {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (fun w => ‖jensenExtremal r w‖ ^ 2) 0 1 = r⁻¹ ^ 2 :=
  circleAverage_const_on_circle fun x hx => by
    rw [norm_jensenExtremal hr0 hr1 (by simpa using hx)]

theorem circleAverage_log_norm_jensenExtremal {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (fun w => Real.log ‖jensenExtremal r w‖) 0 1 = Real.log r⁻¹ :=
  circleAverage_const_on_circle fun x hx => by
    rw [norm_jensenExtremal hr0 hr1 (by simpa using hx)]

/-- **Jensen is sharp for holomorphic-moment data.** For every `c > 1` there is `F`, holomorphic
on a neighbourhood of the closed unit disc, whose boundary law has all holomorphic moments `1`,
mean square `c` and log-mean `½ log c`, the Jensen ceiling. -/
theorem exists_jensen_extremal {c : ℝ} (hc : 1 < c) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (closedBall 0 1) ∧
      (∀ k : ℕ, circleAverage (fun w => F w ^ k) 0 1 = 1) ∧
      circleAverage (fun w => ‖F w‖ ^ 2) 0 1 = c ∧
      circleAverage (fun w => Real.log ‖F w‖) 0 1 = Real.log c / 2 := by
  have hs1 : 1 < Real.sqrt c := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one hc
  have hs0 : 0 < Real.sqrt c := zero_lt_one.trans hs1
  set r := (Real.sqrt c)⁻¹ with hr_def
  have hr0 : 0 < r := inv_pos.mpr hs0
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hs1
  have hrinv : r⁻¹ = Real.sqrt c := by rw [hr_def, inv_inv]
  refine ⟨jensenExtremal r, differentiableOn_jensenExtremal hr0.le hr1,
    circleAverage_pow_jensenExtremal hr0 hr1, ?_, ?_⟩
  · rw [circleAverage_sq_norm_jensenExtremal hr0 hr1, hrinv,
      Real.sq_sqrt (zero_le_one.trans hc.le)]
  · rw [circleAverage_log_norm_jensenExtremal hr0 hr1, hrinv, Real.log_sqrt
      (zero_le_one.trans hc.le)]

end

end GaloisForLFunctions.RHTower.WD
