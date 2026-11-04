import GaloisForLFunctions.RHTower.MobiusTwoJetLinearDensity
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall

/-!
# A sieve truncation with logarithmic mass and smaller polynomial error

The sixteenth root of the progression length has logarithm comparable to
that length's logarithm. Its sixth power is negligible against the expected
prime count.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Filter Topology
open _root_.RHTower.Sieve

/-- The floor of the sixteenth root retains logarithmic size and absorbs its sieve error. -/
theorem eventually_progression_truncation :
    ∀ᶠ u : ℝ in atTop,
      1 < u ∧ 1 ≤ ⌊u ^ (1 / 16 : ℝ)⌋₊ ∧
      14 ≤ Real.log (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ∧
      Real.log u / 32 ≤ Real.log (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ∧
      (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) + (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ^ 6 ≤
        u / Real.log u := by
  have hz := (tendsto_log_div_rpow (by norm_num : (0 : ℝ) < 5 / 8)).const_mul 2
  simp only [mul_zero] at hz
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 448,
    hz.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with u hu hlog herr
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hL : 0 < Real.log u := Real.log_pos hu
  have hp1 : 1 ≤ u ^ (1 / 16 : ℝ) := Real.one_le_rpow hu.le (by norm_num)
  have hY1 : 1 ≤ ⌊u ^ (1 / 16 : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast hp1)
  have hY : (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ≤ u ^ (1 / 16 : ℝ) :=
    Nat.floor_le (by positivity)
  have hlower := RHTower.CubicGamma.log_floor_rpow_ge hu.le (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num only at h
    exact h
  refine ⟨hu, hY1, by linarith only [hlower, hlog, hlog2],
    by linarith only [hlower, hlog, hlog2], ?_⟩
  have hY6 : (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ^ 6 ≤ u ^ (3 / 8 : ℝ) := by
    refine (pow_le_pow_left₀ (Nat.cast_nonneg _) hY 6).trans_eq ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
    norm_num
  have hYsmall : (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ≤ u ^ (3 / 8 : ℝ) :=
    hY.trans (Real.rpow_le_rpow_of_exponent_le hu.le (by norm_num))
  have hbase : 2 * Real.log u ≤ u ^ (5 / 8 : ℝ) := by
    apply (div_le_one (Real.rpow_pos_of_pos hu0 (5 / 8))).mp
    simpa only [mul_div_assoc] using herr
  have hpows : u ^ (3 / 8 : ℝ) * u ^ (5 / 8 : ℝ) = u := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hdom : 2 * u ^ (3 / 8 : ℝ) ≤ u / Real.log u := by
    apply (le_div_iff₀ hL).mpr
    have h := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hu0.le (3 / 8))
    rw [hpows] at h
    nlinarith only [h]
  linarith only [hY6, hYsmall, hdom]

#print axioms eventually_progression_truncation

end GaloisForLFunctions.BezoutValuationIncidence
