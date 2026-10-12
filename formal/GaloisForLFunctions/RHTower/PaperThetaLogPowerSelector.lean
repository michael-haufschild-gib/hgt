import GaloisForLFunctions.RHTower.PaperThetaLogPowerDensity
import GaloisForLFunctions.HTGeometry.PaperLogPowerAdmission
import Mathlib.MeasureTheory.Integral.Asymptotics

/-! # Complete logarithmic-power admission for the literal theta quantile mode

For every complex parameter and every finite nonnegative logarithmic power,
admission occurs exactly at zero, on the Xi divisor, or above the sharp tilt
threshold. In particular equality at the threshold is excluded off the divisor.
-/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped NNReal ENNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

def pullbackLogPower (z : ℂ) (a : ℝ≥0) (t : ℝ) : ℝ :=
  ‖flatModePullback z t‖ * Real.log (2 + ‖flatModePullback z t‖) ^ (a : ℝ)

theorem measurable_pullbackLogPower (z : ℂ) (a : ℝ≥0) : Measurable (pullbackLogPower z a) :=
  (measurable_pullback_all z).norm.mul
    ((measurable_const.add (measurable_pullback_all z).norm).log.pow_const (a : ℝ))

theorem integrable_pullbackLogPower_iff_density (z : ℂ) (a : ℝ≥0) :
    Integrable (pullbackLogPower z a) unitIntervalMeasure ↔ Integrable (logPowerDensity z a) := by
  rw [integrable_unitInterval_iff_cdf (measurable_pullbackLogPower z a).aestronglyMeasurable]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [pullbackLogPower, flatModePullback, logPowerDensity, smul_eq_mul]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
  field_simp [(thetaSource.normalized_pos x).ne']

private theorem integrable_logPower_of_energy {z : ℂ} (hz : z = 0 ∨ XiC z = 0) (a : ℝ≥0) :
    Integrable (logPowerDensity z a) := by
  have hp := (memLp_pullback_iff_all z).mpr hz
  have h := integrable_logPower_Lp unitIntervalMeasure (hp.toLp (flatModePullback z)) a
  apply (integrable_pullbackLogPower_iff_density z a).mp
  refine h.congr ?_
  filter_upwards [hp.coeFn_toLp] with t ht
  simp only [pullbackLogPower, ht]

private theorem not_integrable_logPower {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0)
    (a : ℝ≥0) (ha : z.im ≤ 2 * (a : ℝ)) : ¬ Integrable (logPowerDensity z a) := by
  intro hint
  have hC : flatConnection z ≠ 0 := by
    rw [flatConnection_eq_all]
    exact div_ne_zero hXi (by exact_mod_cast thetaSource.mass_ne_zero)
  let c := ‖z‖ * ‖flatConnection z‖ * Real.pi ^ (a : ℝ) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hl : c < ‖z‖ * ‖flatConnection z‖ * Real.pi ^ (a : ℝ) := by
    dsimp [c] at *
    linarith
  have hev := (tendsto_scaled_logPowerDensity hz hXi a).eventually (lt_mem_nhds hl)
  obtain ⟨X, hX⟩ := eventually_atBot.mp (hev.and (eventually_le_atBot (0 : ℝ)))
  have hon : IntegrableOn (fun _ : ℝ => c) (Iic X) := by
    refine (hint.integrableOn (s := Iic X)).mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun x hx => ?_)
    obtain ⟨hlo, hx0⟩ := hX x hx
    rw [Real.norm_eq_abs, abs_of_pos hc]
    have he : Real.exp ((2 * (a : ℝ) - z.im) * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hx0)
    have hle := mul_le_mul_of_nonneg_right he (logPowerDensity_nonneg z a x)
    linarith
  rw [integrableOn_const_iff] at hon
  rcases hon with h0 | hfin
  · exact hc.ne' (by simpa using h0)
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

private theorem integrable_logPower_above {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0)
    (a : ℝ≥0) (ha : 2 * (a : ℝ) < z.im) : Integrable (logPowerDensity z a) := by
  have hl := tendsto_scaled_logPowerDensity hz hXi a
  have hd : Tendsto (fun x : ℝ => logPowerDensity z a x /
      Real.exp ((z.im - 2 * (a : ℝ)) * x)) atBot
        (𝓝 (‖z‖ * ‖flatConnection z‖ * Real.pi ^ (a : ℝ))) := by
    refine hl.congr fun x => ?_
    rw [div_eq_mul_inv, ← Real.exp_neg]
    have he : -((z.im - 2 * (a : ℝ)) * x) = (2 * (a : ℝ) - z.im) * x := by ring
    rw [he, mul_comm]
  have ho := isBigO_of_div_tendsto_nhds
    (Eventually.of_forall fun x hx => (Real.exp_ne_zero _ hx).elim) _ hd
  have hc : LocallyIntegrable (logPowerDensity z a) volume :=
    (continuous_logPowerDensity z a).locallyIntegrable
  refine hc.integrable_of_isBigO_atBot_atTop ho
    ⟨Iic 0, Iic_mem_atBot 0, integrableOn_exp_mul_Iic (sub_pos.mpr ha) 0⟩
    (logPowerDensity_isBigO_right z a) ⟨Ioi 0, Ioi_mem_atTop 0, ?_⟩
  simpa using (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0)

/-- Sharp, unconditional classification over the entire spectral plane. -/
theorem integrable_logPowerDensity_iff (z : ℂ) (a : ℝ≥0) :
    Integrable (logPowerDensity z a) ↔ z = 0 ∨ XiC z = 0 ∨ 2 * (a : ℝ) < z.im := by
  by_cases hz : z = 0
  · exact iff_of_true (integrable_logPower_of_energy (Or.inl hz) a) (Or.inl hz)
  by_cases hXi : XiC z = 0
  · exact iff_of_true (integrable_logPower_of_energy (Or.inr hXi) a) (Or.inr (Or.inl hXi))
  simp only [hz, hXi, false_or]
  constructor
  · intro h
    by_contra ha
    exact not_integrable_logPower hz hXi a (le_of_not_gt ha) h
  · exact integrable_logPower_above hz hXi a

/-- The sharp criterion holds in the original quantile coordinate with its actual amplitude. -/
theorem integrable_pullbackLogPower_iff (z : ℂ) (a : ℝ≥0) :
    Integrable (pullbackLogPower z a) unitIntervalMeasure ↔
      z = 0 ∨ XiC z = 0 ∨ 2 * (a : ℝ) < z.im := by
  rw [integrable_pullbackLogPower_iff_density, integrable_logPowerDensity_iff]

/-- Within this exact family, all finite logarithmic powers recover the L² domain. -/
theorem memLp_iff_all_logPowers (z : ℂ) :
    MemLp (flatModePullback z) 2 unitIntervalMeasure ↔
      ∀ a : ℝ≥0, Integrable (pullbackLogPower z a) unitIntervalMeasure := by
  rw [memLp_pullback_iff_all]
  constructor
  · intro hz a
    exact (integrable_pullbackLogPower_iff z a).mpr
      (hz.elim Or.inl (fun h => Or.inr (Or.inl h)))
  · intro h
    let a : ℝ≥0 := ⟨|z.im| + 1, by positivity⟩
    rcases (integrable_pullbackLogPower_iff z a).mp (h a) with hz | hXi | hlt
    · exact Or.inl hz
    · exact Or.inr hXi
    · change 2 * (|z.im| + 1) < z.im at hlt
      linarith [le_abs_self z.im, abs_nonneg z.im]

end RHTower.PaperThetaEndpoint
