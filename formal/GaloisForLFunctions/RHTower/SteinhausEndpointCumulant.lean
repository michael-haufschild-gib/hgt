import GaloisForLFunctions.RHTower.SteinhausProfileLogIntegral
import GaloisForLFunctions.HTGeometry.SteinhausSharpAsymptotic

/-!
# The high-coherence endpoint of the cumulant

The sharp Bessel asymptotic transfers to the mixture with NO dominated convergence: the profile is
bounded below by `1 − α`, so `λ w_α(v) ≥ λ(1−α) → ∞` *uniformly* in `v`, and the error of the
sharp asymptotic is therefore uniformly small on the whole profile.  Integrating

`log I₀(y) = y − ½log(2πy) + e(y)`

against the unit-mass profile, with `∫₀¹ log w_α = log(1−α) + α`, gives the card's `(29)`:

`Λ_α(λ) = λ − ½log(2πλ) − ½log(1−α) − α/2 + o(1)`.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The error of the one-circle cumulant against its sharp asymptotic. -/
def steinhausCumulantError (y : ℝ) : ℝ :=
  steinhausLogLaplace y - y + (1 / 2) * Real.log (2 * Real.pi * y)

theorem tendsto_steinhausCumulantError :
    Tendsto steinhausCumulantError atTop (𝓝 0) :=
  tendsto_steinhausLogLaplace_sub_sharp

/-- The profile never drops below `1 − α`. -/
theorem le_weightProfile {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) {v : ℝ} (hv : 0 < v)
    (hv1 : v ≤ 1) : 1 - α ≤ weightProfile α v := by
  have h1 : (1 : ℝ) ≤ v ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
  have h2 : (0 : ℝ) < 1 - α := by linarith
  rw [weightProfile]
  nlinarith [h1, h2]

/-- The card's `(29)`, as an exact identity for the deficit. -/
theorem rvCumulant_deficit_eq {α : ℝ} (hα : α < 1) {lam : ℝ} (hlam : 0 < lam) :
    rvCumulant α lam
        - (lam - (1 / 2) * Real.log (2 * Real.pi * lam)
            - (1 / 2) * Real.log (1 - α) - α / 2)
      = ∫ v in (0 : ℝ)..1, steinhausCumulantError (lam * weightProfile α v) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlin : IntervalIntegrable (fun v : ℝ => lam * weightProfile α v) volume 0 1 :=
    (intervalIntegrable_weightProfile hα).const_mul _
  have hlogw : IntervalIntegrable (fun v : ℝ => Real.log (weightProfile α v)) volume 0 1 :=
    intervalIntegrable_log_weightProfile hα
  have hlogfull : IntervalIntegrable
      (fun v : ℝ => (1 / 2) * (Real.log (2 * Real.pi * lam) + Real.log (weightProfile α v)))
      volume 0 1 := (intervalIntegrable_const.add hlogw).const_mul _
  have hcum := intervalIntegrable_rvCumulant_integrand hα lam
  have hcongr : (∫ v in (0 : ℝ)..1, steinhausCumulantError (lam * weightProfile α v))
      = ∫ v in (0 : ℝ)..1, (steinhausLogLaplace (lam * weightProfile α v)
          - lam * weightProfile α v
          + (1 / 2) * (Real.log (2 * Real.pi * lam) + Real.log (weightProfile α v))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with v hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have hv0 : 0 < v := hv.1
    have hw : 0 < weightProfile α v := weightProfile_pos hα hv0
    simp only [steinhausCumulantError]
    rw [show 2 * Real.pi * (lam * weightProfile α v)
          = (2 * Real.pi * lam) * weightProfile α v by ring,
      Real.log_mul (by positivity) hw.ne']
  have hsplit : (∫ v in (0 : ℝ)..1, steinhausCumulantError (lam * weightProfile α v))
      = (∫ v in (0 : ℝ)..1, steinhausLogLaplace (lam * weightProfile α v))
        - (∫ v in (0 : ℝ)..1, lam * weightProfile α v)
        + ∫ v in (0 : ℝ)..1,
            (1 / 2) * (Real.log (2 * Real.pi * lam) + Real.log (weightProfile α v)) := by
    rw [hcongr, intervalIntegral.integral_add (hcum.sub hlin) hlogfull,
      intervalIntegral.integral_sub hcum hlin]
  have hsecond : (∫ v in (0 : ℝ)..1, lam * weightProfile α v) = lam := by
    rw [intervalIntegral.integral_const_mul, integral_weightProfile hα, mul_one]
  have hthird : (∫ v in (0 : ℝ)..1,
        (1 / 2) * (Real.log (2 * Real.pi * lam) + Real.log (weightProfile α v)))
      = (1 / 2) * (Real.log (2 * Real.pi * lam) + (Real.log (1 - α) + α)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const hlogw,
      intervalIntegral.integral_const, integral_log_weightProfile hα]
    norm_num
  rw [hsplit, hsecond, hthird, rvCumulant]
  ring


/-- **The card's `(29)`:** `Λ_α(λ) = λ − ½log(2πλ) − ½log(1−α) − α/2 + o(1)`. -/
theorem tendsto_rvCumulant_deficit {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) :
    Tendsto (fun lam : ℝ => rvCumulant α lam
        - (lam - (1 / 2) * Real.log (2 * Real.pi * lam)
            - (1 / 2) * Real.log (1 - α) - α / 2)) atTop (𝓝 0) := by
  have hα1 : (0 : ℝ) < 1 - α := by linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.1 tendsto_steinhausCumulantError (ε / 2) (by linarith)
  refine ⟨max 1 (Y / (1 - α)), fun lam hlam => ?_⟩
  have hlam1 : (1 : ℝ) ≤ lam := le_trans (le_max_left _ _) hlam
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam1
  have hlamY : Y / (1 - α) ≤ lam := le_trans (le_max_right _ _) hlam
  have hbound : ∀ v ∈ uIoc (0 : ℝ) 1,
      ‖steinhausCumulantError (lam * weightProfile α v)‖ ≤ ε / 2 := by
    intro v hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have hw : 1 - α ≤ weightProfile α v := le_weightProfile hα0 hα hv.1 hv.2
    have hge : Y ≤ lam * weightProfile α v := by
      rw [div_le_iff₀ hα1] at hlamY
      nlinarith [hw, hlam0]
    have := hY (lam * weightProfile α v) hge
    rw [Real.dist_eq, sub_zero] at this
    rw [Real.norm_eq_abs]
    linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.dist_eq, sub_zero, rvCumulant_deficit_eq hα hlam0]
  rw [Real.norm_eq_abs] at hnorm
  have habs : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [habs, mul_one] at hnorm
  linarith

end

end HTGeometry
