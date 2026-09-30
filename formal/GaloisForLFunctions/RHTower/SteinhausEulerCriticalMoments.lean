import GaloisForLFunctions.RHTower.SteinhausEulerCriticalMass
import Mathlib.MeasureTheory.Integral.MeanInequalities

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The exact unit first moment controls every smaller moment by one tail probability. -/
theorem lintegral_steinhausEulerCriticalMass_rpow_le (N : ℕ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (ε : ℝ≥0∞) :
    (∫⁻ ω, steinhausEulerCriticalMass N ω ^ q ∂steinhausMeasure) ≤
      ε ^ q + steinhausMeasure {ω | ε ≤ steinhausEulerCriticalMass N ω} ^ (1 - q) := by
  let B := {ω | ε ≤ steinhausEulerCriticalMass N ω}
  let g : Omega → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hB : MeasurableSet B :=
    measurableSet_le measurable_const (measurable_steinhausEulerCriticalMass N)
  have hg : Measurable g := measurable_const.indicator hB
  have hpt (ω : Omega) : steinhausEulerCriticalMass N ω ^ q ≤
      ε ^ q + steinhausEulerCriticalMass N ω ^ q * g ω ^ (1 - q) := by
    by_cases hω : ω ∈ B
    · simp only [g, Set.indicator_of_mem hω, ENNReal.one_rpow, mul_one]
      calc
        _ = 0 + steinhausEulerCriticalMass N ω ^ q := (zero_add _).symm
        _ ≤ _ := add_le_add bot_le le_rfl
    · simp only [g, Set.indicator_of_notMem hω,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hq1), mul_zero, add_zero]
      exact ENNReal.rpow_le_rpow (le_of_not_ge hω) hq.le
  calc
    _ ≤ ∫⁻ ω, ε ^ q + steinhausEulerCriticalMass N ω ^ q * g ω ^ (1 - q)
        ∂steinhausMeasure := lintegral_mono hpt
    _ = ε ^ q + ∫⁻ ω, steinhausEulerCriticalMass N ω ^ q * g ω ^ (1 - q)
        ∂steinhausMeasure := by
      rw [lintegral_add_left measurable_const, lintegral_const]
      simp
    _ ≤ ε ^ q + (∫⁻ ω, steinhausEulerCriticalMass N ω ∂steinhausMeasure) ^ q *
        (∫⁻ ω, g ω ∂steinhausMeasure) ^ (1 - q) :=
      add_le_add le_rfl (ENNReal.lintegral_mul_norm_pow_le
        (measurable_steinhausEulerCriticalMass N).aemeasurable hg.aemeasurable
        hq.le (sub_pos.mpr hq1).le (by ring))
    _ = _ := by
      rw [lintegral_steinhausEulerCriticalMass]
      simp [g, lintegral_indicator hB, B]

/-- Every subunit moment of the literal critical mass vanishes along all cutoffs. -/
theorem tendsto_lintegral_steinhausEulerCriticalMass_rpow {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N => ∫⁻ ω, steinhausEulerCriticalMass N ω ^ q ∂steinhausMeasure)
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  by_cases htop : δ = ∞
  · subst δ
    exact ⟨0, fun _ _ => le_top⟩
  let b := δ / 2
  have hb : 0 < b := ENNReal.div_pos hδ.ne' (by norm_num)
  have hbtop : b ≠ ∞ := by dsimp [b]; finiteness
  let ε := b ^ (1 / q)
  have hε : 0 < ε := ENNReal.rpow_pos hb hbtop
  have hεtop : ε ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hbtop
  have hεq : ε ^ q = b := by
    rw [← ENNReal.rpow_mul]
    have hcancel : 1 / q * q = 1 := by field_simp
    rw [hcancel, ENNReal.rpow_one]
  have hprob : Tendsto (fun N => steinhausMeasure {ω | ε ≤ steinhausEulerCriticalMass N ω})
      atTop (𝓝 0) := by
    have h := tendsto_measure_steinhausEulerCriticalMass_ge (ENNReal.toReal_pos hε.ne' hεtop)
    simpa only [ENNReal.ofReal_toReal hεtop] using h
  have hpow : Tendsto (fun N => steinhausMeasure {ω | ε ≤ steinhausEulerCriticalMass N ω} ^ (1 - q))
      atTop (𝓝 0) := by
    simpa only [ENNReal.zero_rpow_of_pos (sub_pos.mpr hq1)] using
      hprob.ennrpow_const (1 - q)
  obtain ⟨N₀, hN₀⟩ := ENNReal.tendsto_atTop_zero.mp hpow b hb
  refine ⟨N₀, fun N hN => ?_⟩
  calc
    _ ≤ ε ^ q + steinhausMeasure {ω | ε ≤ steinhausEulerCriticalMass N ω} ^ (1 - q) :=
      lintegral_steinhausEulerCriticalMass_rpow_le N hq hq1 ε
    _ ≤ b + b := add_le_add hεq.le (hN₀ N hN)
    _ = δ := ENNReal.add_halves δ

/-- In particular, the square-root energy moment needed by the arithmetic reduction vanishes. -/
theorem tendsto_lintegral_steinhausEulerCriticalMass_sqrt :
    Tendsto (fun N => ∫⁻ ω, steinhausEulerCriticalMass N ω ^ (1 / 2 : ℝ) ∂steinhausMeasure)
      atTop (𝓝 0) :=
  tendsto_lintegral_steinhausEulerCriticalMass_rpow (by norm_num) (by norm_num)

end RHTower
