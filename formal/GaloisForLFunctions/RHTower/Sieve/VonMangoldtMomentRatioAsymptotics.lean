import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSelfConvHarmonicSquareAsymptotic
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSelfConvCrossHarmonicBound

/-!
# Asymptotics of von Mangoldt harmonic moments

Normalized limits of two harmonic moments of the von Mangoldt function:
`∑_{2 ≤ k ≤ N} Λ(k)^2 / k ~ (log N)^2 / 2`, and the cross moment
`∑_{2 ≤ k ≤ N} Λ(k) (Λ * Λ)(k) / k = o((log N)^3)`. Both follow from explicit error bounds
(`39 log N + 25` and `24 log N (1 + log N)`) proved elsewhere.

## Main results

- `tendsto_vonMangoldtHarmonicSquareSum_div_logSquare`:
  `(∑_{2 ≤ k ≤ N} Λ(k)^2/k) / (log N)^2 → 1/2`.
- `tendsto_vonMangoldtSelfConvCrossHarmonicSum_div_logCube`:
  `(∑_{2 ≤ k ≤ N} Λ(k) (Λ * Λ)(k)/k) / (log N)^3 → 0`.

## Hypotheses

Unconditional.
-/

noncomputable section

open Filter Topology ArithmeticFunction Finset
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

private theorem tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_inv_log_nat_zero :
    Tendsto (fun N : ℕ => (1 : ℝ) / Real.log N) atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_log_nat_atTop

/-- The harmonic square moment of `Λ` satisfies `(∑_{2 ≤ k ≤ N} Λ(k)^2/k) / (log N)^2 → 1/2`. -/
theorem tendsto_vonMangoldtHarmonicSquareSum_div_logSquare :
    Tendsto (fun N : ℕ =>
      vonMangoldtHarmonicSquareSum N / Real.log N ^ (2 : ℕ))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hbound : Tendsto (fun N : ℕ =>
      39 * ((1 : ℝ) / Real.log N) +
        25 * ((1 : ℝ) / Real.log N) ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := (39 : ℝ))).mul tendsto_inv_log_nat_zero).add
      ((tendsto_const_nhds (x := (25 : ℝ))).mul
        (tendsto_inv_log_nat_zero.pow 2))
  have herr : Tendsto (fun N : ℕ =>
      (vonMangoldtHarmonicSquareSum N - Real.log N ^ (2 : ℕ) / 2) /
        Real.log N ^ (2 : ℕ)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hraw := abs_vonMangoldtHarmonicSquareSum_sub_le N (by omega)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlog 2)]
    calc
      |vonMangoldtHarmonicSquareSum N - Real.log N ^ (2 : ℕ) / 2| /
          Real.log N ^ (2 : ℕ) ≤
        (39 * Real.log N + 25) / Real.log N ^ (2 : ℕ) :=
          div_le_div_of_nonneg_right hraw (pow_pos hlog 2).le
      _ = 39 * ((1 : ℝ) / Real.log N) +
          25 * ((1 : ℝ) / Real.log N) ^ (2 : ℕ) := by
            field_simp [hlog.ne']
  have hsum := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add herr
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp [hlog]
    ring)

theorem vonMangoldtSelfConvCrossHarmonicSum_nonneg (N : ℕ) :
    0 ≤ vonMangoldtSelfConvCrossHarmonicSum N := by
  rw [vonMangoldtSelfConvCrossHarmonicSum]
  exact Finset.sum_nonneg fun k hk =>
    div_nonneg (mul_nonneg vonMangoldt_nonneg (vonMangoldtSelfConv_nonneg k)) (by positivity)

/-- The cross moment `∑_{2 ≤ k ≤ N} Λ(k) (Λ * Λ)(k)/k` is `o((log N)^3)`. -/
theorem tendsto_vonMangoldtSelfConvCrossHarmonicSum_div_logCube :
    Tendsto (fun N : ℕ =>
      vonMangoldtSelfConvCrossHarmonicSum N / Real.log N ^ (3 : ℕ))
      atTop (nhds 0) := by
  have hupper : Tendsto (fun N : ℕ =>
      24 * (((1 : ℝ) / Real.log N) ^ (2 : ℕ) +
        (1 : ℝ) / Real.log N)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (24 : ℝ))).mul
      ((tendsto_inv_log_nat_zero.pow 2).add tendsto_inv_log_nat_zero)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    exact div_nonneg (vonMangoldtSelfConvCrossHarmonicSum_nonneg N)
      (pow_pos hlog 3).le
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hraw := vonMangoldtSelfConvCrossHarmonicSum_le N (by omega)
    calc
      vonMangoldtSelfConvCrossHarmonicSum N / Real.log N ^ (3 : ℕ) ≤
          (24 * Real.log N * (1 + Real.log N)) / Real.log N ^ (3 : ℕ) :=
        div_le_div_of_nonneg_right hraw (pow_pos hlog 3).le
      _ = 24 * (((1 : ℝ) / Real.log N) ^ (2 : ℕ) +
          (1 : ℝ) / Real.log N) := by
            field_simp [hlog.ne']

end RHTower.Sieve
