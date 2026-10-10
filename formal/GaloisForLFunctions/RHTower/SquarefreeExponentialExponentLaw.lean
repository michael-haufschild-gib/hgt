import GaloisForLFunctions.RHTower.SquarefreeExponentialRH

/-!
# The exponent law for the exponentially weighted squarefree count

Let `A(t) = Σ_{n ≥ 1} μ(n)² e^{-nt}`, `c = 6/π²` and `Θ = sup {Re ρ : ζ(ρ) = 0}`
(`zetaZeroAbscissa`).

* **Upper law** (`expBound_zetaZeroAbscissa`). Unconditionally
  `A(t) - c/t = O(t^{-Θ/2-ε})` for every `ε > 0`.
* **Exactness below the cascade fixed point** (`not_expBound_of_lt_half_zetaZeroAbscissa`). If
  `Θ ≤ 2/3`, then `A(t) - c/t ≠ O(t^{-α})` for every `α < Θ/2`. So the exponent of the smoothed
  squarefree error is exactly `Θ/2` when `Θ ≤ 2/3`.

The threshold `2/3` is the fixed point of the halving cascade `z ↦ 1 - z/2`. A bound `t^{-α}`
excludes zeros only in the band `2α < Re s < 2 - 4α`, which contains the frontier `Re s = Θ` exactly
when `Θ ≤ 2 - 2Θ`. Beyond `2/3` the squarefree count can only miss frontier zeros whose halves
`ρ/2` are again zeros. For Mertens the exponent law is exact unconditionally; for this
`ζ(2s)`-denominator receiver exactness stops at the cascade fixed point.
-/

open Filter Topology MeasureTheory Set Complex
open scoped ArithmeticFunction.Moebius

namespace RHTower.SquarefreeExponential

noncomputable section

/-- **Upper law at the zero frontier.** -/
theorem expBound_zetaZeroAbscissa {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖profile t - density / t‖ ≤ C * t ^ (-(zetaZeroAbscissa / 2 + ε)) := by
  set Θ : ℝ := zetaZeroAbscissa with hΘdef
  have hΘ0 : 0 < Θ := zetaZeroAbscissa_pos
  have hΘ1 : Θ ≤ 1 := zetaZeroAbscissa_le_one
  set δ : ℝ := min ε (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hmain : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖profile t - density / t‖ ≤ C * t ^ (-(Θ / 2 + δ)) := by
    by_cases hcase : Θ + δ ≤ 1
    · obtain ⟨B, hB, hMB⟩ := mobiusMertens_subpower_zetaZeroAbscissa δ hδ0
      have hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ (Θ + δ) := fun n => by
        rw [← norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal]; exact hMB n
      exact abs_profile_sub_le_of_mertens (θ := Θ + δ) (β := Θ / 2 + δ) (by linarith) hcase
        (by linarith) (by linarith) hB hM
    · have hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ 1 * ((n : ℝ) + 1) ^ (1 : ℝ) := fun n => by
        rw [one_mul, Real.rpow_one]
        have h := abs_mertensFunctionReal_le (n : ℝ)
        rw [Nat.floor_natCast] at h
        linarith
      exact abs_profile_sub_le_of_mertens (θ := 1) (β := Θ / 2 + δ) zero_le_one le_rfl
        (by linarith) (by linarith) zero_le_one hM
  obtain ⟨C, hC⟩ := hmain
  refine ⟨|C|, fun t ht => ?_⟩
  calc ‖profile t - density / t‖ ≤ C * t ^ (-(Θ / 2 + δ)) := hC t ht
    _ ≤ |C| * t ^ (-(Θ / 2 + δ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht.1.le _)
    _ ≤ |C| * t ^ (-(Θ / 2 + ε)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)) (abs_nonneg C)

/-- **Exactness below the cascade fixed point.** If `Θ ≤ 2/3`, no bound `t^{-α}` with `α < Θ/2`
holds. -/
theorem not_expBound_of_lt_half_zetaZeroAbscissa (hΘ : zetaZeroAbscissa ≤ 2 / 3) {α : ℝ}
    (hα : α < zetaZeroAbscissa / 2) :
    ¬ ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α) := by
  rintro ⟨C, hC⟩
  have hΘ0 : 0 < zetaZeroAbscissa := zetaZeroAbscissa_pos
  set α' : ℝ := max α 0 with hα'
  have hα'0 : 0 ≤ α' := le_max_right _ _
  have hα'Θ : 2 * α' < zetaZeroAbscissa := by
    rcases le_total α 0 with h | h
    · rw [hα', max_eq_right h]; linarith
    · rw [hα', max_eq_left h]; linarith
  have hC' : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ |C| * t ^ (-α') := by
    intro t ht
    calc ‖profile t - density / t‖ ≤ C * t ^ (-α) := hC t ht
      _ ≤ |C| * t ^ (-α) := mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg ht.1.le _)
      _ ≤ |C| * t ^ (-α') := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith [le_max_left α 0]))
          (abs_nonneg C)
  obtain ⟨ρ, hz, hρ1, hρ⟩ := exists_zetaZero_mem_openStrip_lt_re hα'Θ
  have hρΘ := re_le_zetaZeroAbscissa hz
  exact riemannZeta_ne_zero_of_expBound hα'0 (by linarith) hC' hρ (by linarith) hz

end

end RHTower.SquarefreeExponential
