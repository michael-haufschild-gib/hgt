import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerTailJetMesh

/-!
# The logarithmic finite part of the critical archimedean comb

The critical increment has harmonic weight. Its row error is bounded by
the sum of powers `N⁻¹` and `N⁻¹ᐟ²`, so the weighted error is absolutely
summable. Telescoping then removes the sole logarithmic divergence.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Summable correction to the critical harmonic row. -/
def criticalPowerTailArchimedeanError (N : ℕ) : ℝ :=
  (powerTailArchimedeanRow (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2)) / (N + 1)

theorem summable_criticalPowerTailArchimedeanError :
    Summable criticalPowerTailArchimedeanError := by
  have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.2 (by norm_num))
  have h3 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.2 (by norm_num))
  have hmajor := (h2.mul_left (5 / 2 : ℝ)).add (h3.mul_left 4)
  apply summable_norm_iff.mp
  apply hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hhalf : (1 / ((n : ℝ) + 1)) ^ (1 / 2 : ℝ) =
      ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
  rw [criticalPowerTailArchimedeanError, Real.norm_eq_abs, abs_div, abs_of_pos hn]
  calc
    _ ≤ ((5 / 2 : ℝ) / (n + 1) +
        4 * (1 / (n + 1 : ℝ)) ^ (1 / 2 : ℝ)) / (n + 1) :=
      div_le_div_of_nonneg_right (abs_criticalPowerTailArchimedeanRow_error_le n) hn.le
    _ = (5 / 2 : ℝ) * ((n : ℝ) + 1) ^ (-1 : ℝ) * ((n : ℝ) + 1) ^ (-1 : ℝ) +
        4 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) + 1) ^ (-1 : ℝ) := by
      rw [hhalf]
      simp only [Real.rpow_neg_one]
      ring
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_one, mul_assoc, ← Real.rpow_add hn]
      norm_num

private theorem criticalPowerTailArchimedeanError_eq_increment (N : ℕ) :
    criticalPowerTailArchimedeanError N =
      powerTailArchimedean (1 / 2) (N + 1) - powerTailArchimedean (1 / 2) N -
        powerTailArchimedeanRowLimit (1 / 2) / (N + 1) := by
  have hw : powerTailWeight (1 / 2) (N + 1) ^ 2 = 1 / ((N : ℝ) + 1) := by
    rw [powerTailWeight, sq, ← Real.rpow_add (by positivity)]
    norm_num [Real.rpow_neg_one]
  rw [powerTailArchimedean_increment_profile, hw]
  change (powerTailArchimedeanRow (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2)) /
      (N + 1) = (1 / ((N : ℝ) + 1)) * powerTailArchimedeanRow (1 / 2) N -
        powerTailArchimedeanRowLimit (1 / 2) / (N + 1)
  ring

/-- The finite critical archimedean sum is a harmonic main term plus
the literal partial sum of its summable row errors. -/
theorem sum_criticalPowerTailArchimedeanError (N : ℕ) :
    (∑ n ∈ range N, criticalPowerTailArchimedeanError n) =
      powerTailArchimedean (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2) * harm N := by
  induction N with
  | zero => simp [powerTailArchimedean, harm]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, criticalPowerTailArchimedeanError_eq_increment, harm_succ]
      ring

/-- Constant left after removing the critical archimedean logarithm. -/
def criticalPowerTailArchimedeanFinitePart : ℝ :=
  (∑' n : ℕ, criticalPowerTailArchimedeanError n) +
    powerTailArchimedeanRowLimit (1 / 2) * Real.eulerMascheroniConstant

/-- The critical archimedean comb has an actual logarithmic finite part. -/
theorem tendsto_criticalPowerTailArchimedean_finitePart :
    Tendsto (fun N : ℕ => powerTailArchimedean (1 / 2) N -
      powerTailArchimedeanRowLimit (1 / 2) * Real.log N) atTop
        (𝓝 criticalPowerTailArchimedeanFinitePart) := by
  have hs := summable_criticalPowerTailArchimedeanError.hasSum.tendsto_sum_nat
  have hh := tendsto_harm_sub_log.const_mul (powerTailArchimedeanRowLimit (1 / 2))
  apply (hs.add hh).congr
  intro N
  rw [sum_criticalPowerTailArchimedeanError]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
