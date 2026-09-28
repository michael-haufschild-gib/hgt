import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoveryDensitySeries

/-!
# The arcsine-mixture potential

`g(a,t) = (max(a,t) + √(t² - a²))/2`; `log g(a,t)` is the logarithmic potential at `t ≥ 0` of the
arcsine law on `[-a, a]`.  For the density `h` of `RecoveryDensitySeries`, `0 < b < 1` and
`0 < t < 1`,

  `∫_0^b log g(a,t) h(a) da = ∫_0^b log(a/2) h(a) da + ∫_0^b A(a,t) h(a) da`,

and the Abel identity gives `∫_0^b A(a,t) h(a) da = -½ log(1-t)` for `t ≤ b`, `< -½ log(1-t)` for
`t > b`.  At the recovery edge `b` (where `I(b) = 3π/2`, so `∫_0^b h = 1`) the constant is
`log C` with `C = (b/2) exp((1/π)∫_0^{π/2} log(1 - b cos s) ds)` and `C²/4 = ρ`: the mixture of arcsine
laws with density `h` is in equilibrium with the field `-½ log(1-t)`, with support `[-b, b]`.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The arcsine gauge `g(a,t) = (max(a,t) + √(t² - a²))/2`. -/
def arcsineGauge (a t : ℝ) : ℝ := (max a t + Real.sqrt (t ^ 2 - a ^ 2)) / 2

theorem arcsineGauge_zero_left {t : ℝ} (ht : 0 ≤ t) : arcsineGauge 0 t = t := by
  simp only [arcsineGauge, max_eq_right ht, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, Real.sqrt_sq ht]
  ring

theorem half_le_arcsineGauge (a t : ℝ) : t / 2 ≤ arcsineGauge a t := by
  unfold arcsineGauge
  have := le_max_right a t
  have := Real.sqrt_nonneg (t ^ 2 - a ^ 2)
  linarith

theorem arcsineGauge_pos {a t : ℝ} (ht : 0 < t) : 0 < arcsineGauge a t :=
  lt_of_lt_of_le (by positivity) (half_le_arcsineGauge a t)

theorem arcsineGauge_of_le {a t : ℝ} (hta : t ≤ a) (ht : 0 ≤ t) : arcsineGauge a t = a / 2 := by
  simp only [arcsineGauge, max_eq_left hta, Real.sqrt_eq_zero'.mpr (by nlinarith :
    t ^ 2 - a ^ 2 ≤ 0), add_zero]

theorem arcsineGauge_self {t : ℝ} (ht : 0 ≤ t) : arcsineGauge t t = t / 2 :=
  arcsineGauge_of_le le_rfl ht

theorem log_arcsineGauge {a t : ℝ} (ha : 0 < a) :
    Real.log (arcsineGauge a t) = Real.log (a / 2) + arcsineExcess a t := by
  have hpos : 0 < max a t + Real.sqrt (t ^ 2 - a ^ 2) :=
    lt_of_lt_of_le ha (le_add_of_le_of_nonneg (le_max_left _ _) (Real.sqrt_nonneg _))
  unfold arcsineGauge arcsineExcess
  rw [Real.log_div hpos.ne' two_ne_zero, Real.log_div ha.ne' two_ne_zero]
  ring

theorem continuous_arcsineGauge (t : ℝ) : Continuous fun a => arcsineGauge a t := by
  unfold arcsineGauge
  exact ((continuous_id.max continuous_const).add (by fun_prop)).div_const 2

theorem arcsineGauge_antitoneOn {t : ℝ} :
    AntitoneOn (fun a => arcsineGauge a t) (Icc 0 t) := by
  intro x hx y hy hxy
  simp only [arcsineGauge, max_eq_right hx.2, max_eq_right hy.2]
  have := Real.sqrt_le_sqrt (show t ^ 2 - y ^ 2 ≤ t ^ 2 - x ^ 2 by nlinarith [hx.1])
  linarith

theorem arcsineGauge_monotoneOn {t : ℝ} (ht : 0 ≤ t) :
    MonotoneOn (fun a => arcsineGauge a t) (Ici t) := by
  intro x hx y hy hxy
  simp only [arcsineGauge_of_le (mem_Ici.mp hx) ht, arcsineGauge_of_le (mem_Ici.mp hy) ht]
  linarith

/-- The arcsine gauge is smallest at `a = t`. -/
theorem arcsineGauge_self_le {a t : ℝ} (ht : 0 ≤ t) : arcsineGauge t t ≤ arcsineGauge a t := by
  rw [arcsineGauge_self ht]; exact half_le_arcsineGauge a t

/-! ### The capacity constant -/

/-- `C(b) = (b/2) exp((1/π) ∫_0^{π/2} log(1 - b cos s) ds)`. -/
def recoveryCapacity (b : ℝ) : ℝ :=
  b / 2 * Real.exp (1 / π * ∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s))

theorem recoveryCapacity_pos {b : ℝ} (hb : 0 < b) : 0 < recoveryCapacity b :=
  mul_pos (by positivity) (Real.exp_pos _)

theorem log_recoveryCapacity {b : ℝ} (hb : 0 < b) :
    Real.log (recoveryCapacity b) =
      Real.log (b / 2) + 1 / π * ∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s) := by
  rw [recoveryCapacity, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

/-- **`C(b)²/4 = ρ(b)`.** -/
theorem recoveryCapacity_sq_div_four (b : ℝ) : recoveryCapacity b ^ 2 / 4 = recoveryRateFun b := by
  rw [recoveryCapacity, recoveryRateFun, mul_pow, sq (Real.exp _), ← Real.exp_add]
  ring_nf

/-! ### Integrability -/

theorem continuousOn_recoveryDensity_Icc {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ContinuousOn recoveryDensity (uIcc 0 c) := by
  rw [uIcc_of_le hc0]
  exact (continuousOn_recoveryDensity hc0 hc1).mono (Icc_subset_Icc (by linarith) le_rfl)

theorem intervalIntegrable_log_half_mul_recoveryDensity {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    IntervalIntegrable (fun a => Real.log (a / 2) * recoveryDensity a) volume 0 c := by
  have h := (integral_pow_mul_log_half hc0 (by linarith) 0).1
  simp only [pow_zero, one_mul] at h
  exact h.mul_continuousOn (continuousOn_recoveryDensity_Icc hc0.le hc1)

theorem intervalIntegrable_arcsineExcess_mul_recoveryDensity {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    IntervalIntegrable (fun a => arcsineExcess a t * recoveryDensity a) volume 0 c := by
  have hcont : Continuous fun a : ℝ => Real.log (max a t + Real.sqrt (t ^ 2 - a ^ 2)) :=
    Continuous.log ((continuous_id.max continuous_const).add (by fun_prop)) fun a =>
      (lt_of_lt_of_le ht (le_add_of_le_of_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))).ne'
  exact ((hcont.intervalIntegrable 0 c).sub intervalIntegrable_log').mul_continuousOn
    (continuousOn_recoveryDensity_Icc hc0 hc1)

theorem intervalIntegrable_log_arcsineGauge_mul_recoveryDensity {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    IntervalIntegrable (fun a => Real.log (arcsineGauge a t) * recoveryDensity a) volume 0 c :=
  (((continuous_arcsineGauge t).log fun _ => (arcsineGauge_pos ht).ne').continuousOn.mul
    (continuousOn_recoveryDensity_Icc hc0 hc1)).intervalIntegrable

/-! ### The Abel identity on `[0, b]` -/

theorem integral_arcsineExcess_mul_recoveryDensity_of_le {b t : ℝ} (hb1 : b < 1) (ht0 : 0 < t)
    (htb : t ≤ b) :
    ∫ a in (0 : ℝ)..b, arcsineExcess a t * recoveryDensity a = -Real.log (1 - t) / 2 := by
  have ht1 : t < 1 := htb.trans_lt hb1
  rw [← integral_add_adjacent_intervals
    (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 ht0.le ht1)
    (b := t) (c := b) ?_, integral_arcsineExcess_mul_recoveryDensity ht0 ht1]
  · have hz : ∫ a in t..b, arcsineExcess a t * recoveryDensity a = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun a ha => ?_]
      · simp
      rw [uIcc_of_le htb] at ha
      simp only [arcsineExcess_of_le ha.1 ht0.le, zero_mul]
    rw [hz, add_zero]
  · exact (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0
      (ht0.le.trans htb) hb1).symm.trans
      (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 ht0.le ht1) |>.symm

theorem integral_arcsineExcess_mul_recoveryDensity_lt {b t : ℝ} (hb0 : 0 < b) (hbt : b < t)
    (ht1 : t < 1) :
    ∫ a in (0 : ℝ)..b, arcsineExcess a t * recoveryDensity a < -Real.log (1 - t) / 2 := by
  have ht0 : 0 < t := hb0.trans hbt
  rw [← integral_arcsineExcess_mul_recoveryDensity ht0 ht1,
    ← integral_add_adjacent_intervals
      (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 hb0.le (hbt.trans ht1))
      (b := b) (c := t) ((intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 hb0.le
        (hbt.trans ht1)).symm.trans
        (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 ht0.le ht1))]
  have hpos : 0 < ∫ a in b..t, arcsineExcess a t * recoveryDensity a := by
    refine intervalIntegral_pos_of_pos_on ((intervalIntegrable_arcsineExcess_mul_recoveryDensity
      ht0 hb0.le (hbt.trans ht1)).symm.trans
        (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 ht0.le ht1))
      (fun a ha => mul_pos ?_ (recoveryDensity_pos (hb0.le.trans ha.1.le) (ha.2.trans ht1))) hbt
    have ha0 : 0 < a := hb0.trans ha.1
    unfold arcsineExcess
    rw [max_eq_right ha.2.le, sub_pos]
    exact Real.log_lt_log ha0 (lt_of_lt_of_le ha.2 (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
  linarith

theorem integral_arcsineExcess_mul_recoveryDensity_le {b t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ a in (0 : ℝ)..b, arcsineExcess a t * recoveryDensity a ≤ -Real.log (1 - t) / 2 := by
  rcases le_or_gt t b with htb | hbt
  · exact (integral_arcsineExcess_mul_recoveryDensity_of_le hb.2 ht0 htb).le
  · exact (integral_arcsineExcess_mul_recoveryDensity_lt hb.1 hbt ht1).le

/-! ### The mixture potential -/

theorem integral_log_arcsineGauge_mul_recoveryDensity {b t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (ht0 : 0 < t) :
    ∫ a in (0 : ℝ)..b, Real.log (arcsineGauge a t) * recoveryDensity a =
      (∫ a in (0 : ℝ)..b, Real.log (a / 2) * recoveryDensity a) +
        ∫ a in (0 : ℝ)..b, arcsineExcess a t * recoveryDensity a := by
  rw [← integral_add (intervalIntegrable_log_half_mul_recoveryDensity hb.1 hb.2)
    (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 hb.1.le hb.2)]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun a ha => ?_)
  rw [uIoc_of_le hb.1.le] at ha
  rw [log_arcsineGauge ha.1]
  ring

/-- The density `h` has unit mass on `[0, b]` at the recovery edge. -/
theorem integral_recoveryDensity_edge :
    ∫ a in (0 : ℝ)..recoveryEdge, recoveryDensity a = 1 := by
  rw [integral_recoveryDensity recoveryEdge_mem.1.le recoveryEdge_mem.2, recoveryI_edge]
  field_simp
  ring

theorem integral_log_half_mul_recoveryDensity_edge :
    ∫ a in (0 : ℝ)..recoveryEdge, Real.log (a / 2) * recoveryDensity a =
      Real.log (recoveryCapacity recoveryEdge) := by
  rw [integral_log_half_mul_recoveryDensity recoveryEdge_mem, recoveryI_edge,
    log_recoveryCapacity recoveryEdge_mem.1]
  have hπ := Real.pi_pos.ne'
  field_simp
  ring

/-- **Equilibrium on the support.**  For `0 < t ≤ b`,
`∫_0^b log g(a,t) h(a) da = log C - ½ log(1-t)`. -/
theorem recoveryMixturePotential_eq {t : ℝ} (ht0 : 0 < t) (htb : t ≤ recoveryEdge) :
    ∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a t) * recoveryDensity a =
      Real.log (recoveryCapacity recoveryEdge) - Real.log (1 - t) / 2 := by
  rw [integral_log_arcsineGauge_mul_recoveryDensity recoveryEdge_mem ht0,
    integral_log_half_mul_recoveryDensity_edge,
    integral_arcsineExcess_mul_recoveryDensity_of_le recoveryEdge_mem.2 ht0 htb]
  ring

/-- **Strict inequality off the support.**  For `b < t < 1`,
`∫_0^b log g(a,t) h(a) da < log C - ½ log(1-t)`. -/
theorem recoveryMixturePotential_lt {t : ℝ} (hbt : recoveryEdge < t) (ht1 : t < 1) :
    ∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a t) * recoveryDensity a <
      Real.log (recoveryCapacity recoveryEdge) - Real.log (1 - t) / 2 := by
  rw [integral_log_arcsineGauge_mul_recoveryDensity recoveryEdge_mem
      (recoveryEdge_mem.1.trans hbt), integral_log_half_mul_recoveryDensity_edge]
  have := integral_arcsineExcess_mul_recoveryDensity_lt recoveryEdge_mem.1 hbt ht1
  linarith

/-- **The equilibrium inequality** `∫_0^b log g(a,t) h(a) da ≤ log C - ½ log(1-t)`, `0 < t < 1`. -/
theorem recoveryMixturePotential_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a t) * recoveryDensity a ≤
      Real.log (recoveryCapacity recoveryEdge) - Real.log (1 - t) / 2 := by
  rcases le_or_gt t recoveryEdge with htb | hbt
  · exact (recoveryMixturePotential_eq ht0 htb).le
  · exact (recoveryMixturePotential_lt hbt ht1).le

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
