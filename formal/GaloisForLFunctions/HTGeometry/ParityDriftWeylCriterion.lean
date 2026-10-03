import GaloisForLFunctions.HTGeometry.StonehamPairNormality

/-!
# The parity drift from Weyl sums

For any real `x`, if the averaged Weyl sums `N⁻¹ Σ_{n<N} e(k 4ⁿ x)` tend to `0` for every integer
`k ≠ 0`, then `{4ⁿ x}` is equidistributed in `[1/4, 1/2)` and `[1/2, 3/4)` and the parity drift is
`o(N)`.  For `x = π` this is the analytic form of the open core of the Parity-Drift Hypothesis.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.BinaryParityDrift

open StonehamParityDrift DiscreteWeyl

theorem drift_eq_card_sub_card_fract (x : ℝ) (N : ℕ) :
    (drift x N : ℝ) =
      (#{n ∈ range N | Int.fract ((4 : ℝ) ^ n * x) ∈ Set.Ico (1 / 2 : ℝ) (3 / 4)} : ℝ) -
        #{n ∈ range N | Int.fract ((4 : ℝ) ^ n * x) ∈ Set.Ico (1 / 4 : ℝ) (1 / 2)} := by
  have hpt : ∀ n ∈ range N, ((digitWeight (quatDigit x (n + 1)) : ℤ) : ℝ) =
      (if Int.fract ((4 : ℝ) ^ n * x) ∈ Set.Ico (1 / 2 : ℝ) (3 / 4) then 1 else 0) -
        (if Int.fract ((4 : ℝ) ^ n * x) ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) then 1 else 0) := by
    intro n _
    rw [quatDigit_succ_eq_floor_fract]
    exact StonehamPairDrift.digitWeight_floor_four_mul _
  rw [drift_eq_sum_digitWeight, Int.cast_sum, sum_congr rfl hpt, sum_sub_distrib, card_filter,
    card_filter]
  push_cast
  rfl

/-- **Weyl sums decide the drift.**  If `N⁻¹ Σ_{n<N} e(k 4ⁿ x) → 0` for every `k ≠ 0`, the parity
drift of `x` is `o(N)`. -/
theorem tendsto_drift_of_weylSums {x : ℝ}
    (hW : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * ((4 : ℝ) ^ n * x : ℝ))) atTop
      (𝓝 0)) :
    Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 0) := by
  have h2 := tendsto_card_fract_mem_Ico (fun n => (4 : ℝ) ^ n * x) hW (a := 1 / 2) (b := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have h1 := tendsto_card_fract_mem_Ico (fun n => (4 : ℝ) ^ n * x) hW (a := 1 / 4) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have h := h2.sub h1
  rw [show (3 / 4 : ℝ) - 1 / 2 - (1 / 2 - 1 / 4) = 0 by norm_num] at h
  refine h.congr fun N => ?_
  rw [drift_eq_card_sub_card_fract, sub_div]

theorem not_parityDriftHypothesis_of_weylSums {x : ℝ}
    (hW : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * ((4 : ℝ) ^ n * x : ℝ))) atTop
      (𝓝 0)) :
    ¬ ParityDriftHypothesis x :=
  fun h => h (tendsto_drift_of_weylSums hW)

end GaloisForLFunctions.HTGeometry.BinaryParityDrift
