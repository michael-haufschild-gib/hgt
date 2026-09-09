import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMonotonicity

/-!
# Complete ranges of the fixed-charge model-A coexistence curve

Strict monotonicity and exact endpoint limits give every positive
subcritical pressure and temperature exactly once. The small-radius
range lies strictly between the extremal and critical radii, and the
large-radius range is the entire interval above the critical radius.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeAPressure_below_critical (w φ τ : ℝ) :
    egbFixedChargeAPressure w φ τ < egbFixedChargeACriticalPressure w φ :=
  lt_of_lt_of_le (egbFixedChargeAPressure_strictAnti w φ (show τ - 1 < τ by linarith))
    ((egbFixedChargeAPressure_strictAnti w φ).antitone.ge_of_tendsto
      (egbFixedChargeAPressure_critical_limit w φ) (τ - 1))

theorem egbFixedChargeATemperature_below_critical (w φ τ : ℝ) :
    egbFixedChargeATemperature w φ τ < egbFixedChargeACriticalTemperature w φ :=
  lt_of_lt_of_le (egbFixedChargeATemperature_strictAnti w φ (show τ - 1 < τ by linarith))
    ((egbFixedChargeATemperature_strictAnti w φ).antitone.ge_of_tendsto
      (egbFixedChargeATemperature_critical_limit w φ) (τ - 1))

theorem egbFixedChargeASmallRadius_below_critical (w φ τ : ℝ) :
    egbFixedChargeASmallRadius w φ τ < egbFixedChargeACriticalRadius w φ :=
  lt_of_lt_of_le (egbFixedChargeASmallRadius_strictAnti w φ (show τ - 1 < τ by linarith))
    ((egbFixedChargeASmallRadius_strictAnti w φ).antitone.ge_of_tendsto
      (egbFixedChargeASmallRadius_critical_limit w φ) (τ - 1))

theorem egbFixedChargeASmallRadius_above_extremal (w φ τ : ℝ) :
    exp w < egbFixedChargeASmallRadius w φ τ :=
  lt_of_le_of_lt ((egbFixedChargeASmallRadius_strictAnti w φ).antitone.le_of_tendsto
    (egbFixedChargeASmallRadius_cold_limit w φ) (τ + 1))
      (egbFixedChargeASmallRadius_strictAnti w φ (show τ < τ + 1 by linarith))

theorem egbFixedChargeALargeRadius_above_critical (w φ τ : ℝ) :
    egbFixedChargeACriticalRadius w φ < egbFixedChargeALargeRadius w φ τ :=
  lt_of_le_of_lt ((egbFixedChargeALargeRadius_strictMono w φ).monotone.le_of_tendsto
    (egbFixedChargeALargeRadius_critical_limit w φ) (τ - 1))
      (egbFixedChargeALargeRadius_strictMono w φ (show τ - 1 < τ by linarith))

theorem egbFixedChargeACriticalRadius_above_extremal (w φ : ℝ) :
    exp w < egbFixedChargeACriticalRadius w φ :=
  lt_trans (egbFixedChargeASmallRadius_above_extremal w φ 0)
    (egbFixedChargeASmallRadius_below_critical w φ 0)

theorem egbFixedChargeAPressure_range (w φ : ℝ) :
    Set.range (egbFixedChargeAPressure w φ) = Set.Ioo (0) (egbFixedChargeACriticalPressure w φ) := by
  ext y
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨egbFixedChargeAPressure_pos w φ τ, egbFixedChargeAPressure_below_critical w φ τ⟩
  · intro hy
    have hlo : egbFixedChargeAPressure w φ ≤ᶠ[atTop] (fun _ => y) :=
      ((tendsto_order.mp (egbFixedChargeAPressure_cold_limit w φ)).2 y hy.1).mono (fun _ h => h.le)
    have hhi : (fun _ => y) ≤ᶠ[atBot] egbFixedChargeAPressure w φ :=
      ((tendsto_order.mp (egbFixedChargeAPressure_critical_limit w φ)).1 y hy.2).mono (fun _ h => h.le)
    exact intermediate_value_univ₂_eventually₂ (egbFixedChargeAPressure_differentiable w φ).continuous
      continuous_const hlo hhi

theorem egbFixedChargeATemperature_range (w φ : ℝ) :
    Set.range (egbFixedChargeATemperature w φ) = Set.Ioo (0) (egbFixedChargeACriticalTemperature w φ) := by
  ext y
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨egbFixedChargeATemperature_pos w φ τ, egbFixedChargeATemperature_below_critical w φ τ⟩
  · intro hy
    have hlo : egbFixedChargeATemperature w φ ≤ᶠ[atTop] (fun _ => y) :=
      ((tendsto_order.mp (egbFixedChargeATemperature_cold_limit w φ)).2 y hy.1).mono (fun _ h => h.le)
    have hhi : (fun _ => y) ≤ᶠ[atBot] egbFixedChargeATemperature w φ :=
      ((tendsto_order.mp (egbFixedChargeATemperature_critical_limit w φ)).1 y hy.2).mono (fun _ h => h.le)
    exact intermediate_value_univ₂_eventually₂ (egbFixedChargeATemperature_differentiable w φ).continuous
      continuous_const hlo hhi

theorem egbFixedChargeASmallRadius_range (w φ : ℝ) :
    Set.range (egbFixedChargeASmallRadius w φ) = Set.Ioo (exp w) (egbFixedChargeACriticalRadius w φ) := by
  ext y
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨egbFixedChargeASmallRadius_above_extremal w φ τ, egbFixedChargeASmallRadius_below_critical w φ τ⟩
  · intro hy
    have hlo : egbFixedChargeASmallRadius w φ ≤ᶠ[atTop] (fun _ => y) :=
      ((tendsto_order.mp (egbFixedChargeASmallRadius_cold_limit w φ)).2 y hy.1).mono (fun _ h => h.le)
    have hhi : (fun _ => y) ≤ᶠ[atBot] egbFixedChargeASmallRadius w φ :=
      ((tendsto_order.mp (egbFixedChargeASmallRadius_critical_limit w φ)).1 y hy.2).mono (fun _ h => h.le)
    exact intermediate_value_univ₂_eventually₂ (egbFixedChargeASmallRadius_differentiable w φ).continuous
      continuous_const hlo hhi

theorem egbFixedChargeALargeRadius_range (w φ : ℝ) :
    Set.range (egbFixedChargeALargeRadius w φ) = Set.Ioi (egbFixedChargeACriticalRadius w φ) := by
  ext r
  constructor
  · rintro ⟨τ, rfl⟩
    exact egbFixedChargeALargeRadius_above_critical w φ τ
  · intro hr
    have hlo : egbFixedChargeALargeRadius w φ ≤ᶠ[atBot] (fun _ => r) :=
      ((tendsto_order.mp (egbFixedChargeALargeRadius_critical_limit w φ)).2 r hr).mono (fun _ h => h.le)
    have hhi : (fun _ => r) ≤ᶠ[atTop] egbFixedChargeALargeRadius w φ :=
      (egbFixedChargeALargeRadius_cold_limit w φ).eventually (eventually_ge_atTop r)
    exact intermediate_value_univ₂_eventually₂ (egbFixedChargeALargeRadius_differentiable w φ).continuous
      continuous_const hlo hhi

theorem egbFixedChargeAPressure_unique_parameter (w φ s : ℝ) :
    ∃! τ, egbFixedChargeAPressure w φ τ = thermalRatio s * (egbFixedChargeACriticalPressure w φ) := by
  have hc := egbFixedChargeACriticalPressure_pos w φ
  have hy : thermalRatio s * (egbFixedChargeACriticalPressure w φ) ∈ Set.Ioo 0 (egbFixedChargeACriticalPressure w φ) :=
    ⟨mul_pos (thermalRatio_pos s) hc, by nlinarith [thermalRatio_lt_one s]⟩
  rw [← egbFixedChargeAPressure_range w φ] at hy
  obtain ⟨τ, hτ⟩ := hy
  exact ⟨τ, hτ, fun y hy => (egbFixedChargeAPressure_strictAnti w φ).injective (hy.trans hτ.symm)⟩

theorem egbFixedChargeATemperature_unique_parameter (w φ s : ℝ) :
    ∃! τ, egbFixedChargeATemperature w φ τ = thermalRatio s * (egbFixedChargeACriticalTemperature w φ) := by
  have hc := egbFixedChargeACriticalTemperature_pos w φ
  have hy : thermalRatio s * (egbFixedChargeACriticalTemperature w φ) ∈ Set.Ioo 0 (egbFixedChargeACriticalTemperature w φ) :=
    ⟨mul_pos (thermalRatio_pos s) hc, by nlinarith [thermalRatio_lt_one s]⟩
  rw [← egbFixedChargeATemperature_range w φ] at hy
  obtain ⟨τ, hτ⟩ := hy
  exact ⟨τ, hτ, fun y hy => (egbFixedChargeATemperature_strictAnti w φ).injective (hy.trans hτ.symm)⟩

theorem egbFixedChargeASmallRadius_unique_parameter (w φ s : ℝ) :
    ∃! τ, egbFixedChargeASmallRadius w φ τ =
      exp w + thermalRatio s * (egbFixedChargeACriticalRadius w φ - exp w) := by
  have hc := egbFixedChargeACriticalRadius_above_extremal w φ
  have hz := thermalRatio_pos s
  have hzu := thermalRatio_lt_one s
  have hy : exp w + thermalRatio s * (egbFixedChargeACriticalRadius w φ - exp w) ∈
      Set.Ioo (exp w) (egbFixedChargeACriticalRadius w φ) := by
    constructor <;> nlinarith
  rw [← egbFixedChargeASmallRadius_range w φ] at hy
  obtain ⟨τ, hτ⟩ := hy
  exact ⟨τ, hτ, fun y hy => (egbFixedChargeASmallRadius_strictAnti w φ).injective (hy.trans hτ.symm)⟩

theorem egbFixedChargeALargeRadius_unique_parameter (w φ s : ℝ) :
    ∃! τ, egbFixedChargeALargeRadius w φ τ = egbFixedChargeACriticalRadius w φ + exp s := by
  have hy : egbFixedChargeACriticalRadius w φ + exp s ∈ Set.Ioi (egbFixedChargeACriticalRadius w φ) := by
    have hs := exp_pos s
    change egbFixedChargeACriticalRadius w φ < egbFixedChargeACriticalRadius w φ + exp s
    linarith
  rw [← egbFixedChargeALargeRadius_range w φ] at hy
  obtain ⟨τ, hτ⟩ := hy
  exact ⟨τ, hτ, fun y hy => (egbFixedChargeALargeRadius_strictMono w φ).injective (hy.trans hτ.symm)⟩

end GaloisForLFunctions.HTGeometry
