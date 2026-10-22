import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogHarmonicModels
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowThirdMoment

/-!
# Harmonic models for Selberg fourth-power logarithmic main terms

Two harmonic sums of degree four in logarithms that model Selberg sieve main terms:
`selbergOneFourHarmonicMain b c N = ∑_{d ≤ N/c} 4 log(N/(b d))^3 / d` and
`selbergTwoThreeHarmonicMain a b c N = ∑_{d ≤ N/c} 6 log(N/(a d)) log(N/(b d))^2 / d`.
Expanding `log(N/(b d)) = (log N - log b) - log d` writes each as a combination of the harmonic number
`H_{⌊N/c⌋}` and the log-moments `∑_{j ≤ N/c} (log j)^m / j`, `m = 1, 2, 3`. From the asymptotics of
those moments, the sums divided by `(log N)^4` tend to `1` and `3/2` respectively.

## Main results

- `selbergOneFourHarmonicMain_eq_moments`: exact expansion of the `(1,4)` model in harmonic log-moments.
- `selbergTwoThreeHarmonicMain_eq_moments`: exact expansion of the `(2,3)` model.
- `tendsto_selbergOneFourHarmonicMain_div_log_fourth_one`:
  `selbergOneFourHarmonicMain b c N / (log N)^4 → 1` as `N → ∞`.
- `tendsto_selbergTwoThreeHarmonicMain_div_log_fourth_three_halves`:
  `selbergTwoThreeHarmonicMain a b c N / (log N)^4 → 3/2` as `N → ∞`.

## Hypotheses

Unconditional. The parameters `a`, `b`, `c` are positive natural numbers, and the exact expansions
also assume `N > 0`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Harmonic model `∑_{d=1}^{⌊N/c⌋} 4 log(N/(b d))^3 / d`. -/
def selbergOneFourHarmonicMain (b c N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / c),
    4 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ (3 : ℕ) / (d : ℝ)

/-- Harmonic model `∑_{d=1}^{⌊N/c⌋} 6 log(N/(a d)) log(N/(b d))^2 / d`. -/
def selbergTwoThreeHarmonicMain (a b c N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / c),
    6 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
      Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ (2 : ℕ)) / (d : ℝ)

/-- For `b, N > 0`, with `L = log N - log b` and `M_m = ∑_{j ≤ N/c} (log j)^m / j`:
the `(1,4)` model equals `4 (L^3 H_{⌊N/c⌋} - 3 L^2 M_1 + 3 L M_2 - M_3)`. -/
theorem selbergOneFourHarmonicMain_eq_moments
    {b c N : ℕ} (hb : 0 < b) (hN : 0 < N) :
    selbergOneFourHarmonicMain b c N =
      4 * ((Real.log N - Real.log b) ^ (3 : ℕ) * (harmonic (N / c) : ℝ) -
        3 * (Real.log N - Real.log b) ^ (2 : ℕ) *
          harmonicLogWindowMoment 1 0 (N / c) +
        3 * (Real.log N - Real.log b) *
          harmonicLogWindowMoment 2 0 (N / c) -
        harmonicLogWindowMoment 3 0 (N / c)) := by
  rw [selbergOneFourHarmonicMain, ← sum_Icc_one_div_eq_harmonic,
    harmonicLogWindowMoment_zero_eq_sum_Icc,
    harmonicLogWindowMoment_zero_eq_sum_Icc,
    harmonicLogWindowMoment_zero_eq_sum_Icc]
  simp_rw [Finset.mul_sum]
  rw [mul_sub, mul_add, mul_sub]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  push_cast
  rw [Real.log_div hNR.ne' (mul_pos hbR hdR).ne',
    Real.log_mul hbR.ne' hdR.ne']
  ring

/-- For `a, b, N > 0`, with `A = log N - log a`, `B = log N - log b` and `M_m` the harmonic log-moments:
the `(2,3)` model equals `6 (A B^2 H - (B^2 + 2AB) M_1 + (A + 2B) M_2 - M_3)`. -/
theorem selbergTwoThreeHarmonicMain_eq_moments
    {a b c N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    selbergTwoThreeHarmonicMain a b c N =
      6 * ((Real.log N - Real.log a) * (Real.log N - Real.log b) ^ (2 : ℕ) *
          (harmonic (N / c) : ℝ) -
        ((Real.log N - Real.log b) ^ (2 : ℕ) +
          2 * (Real.log N - Real.log a) * (Real.log N - Real.log b)) *
          harmonicLogWindowMoment 1 0 (N / c) +
        ((Real.log N - Real.log a) +
          2 * (Real.log N - Real.log b)) *
          harmonicLogWindowMoment 2 0 (N / c) -
        harmonicLogWindowMoment 3 0 (N / c)) := by
  rw [selbergTwoThreeHarmonicMain, ← sum_Icc_one_div_eq_harmonic,
    harmonicLogWindowMoment_zero_eq_sum_Icc,
    harmonicLogWindowMoment_zero_eq_sum_Icc,
    harmonicLogWindowMoment_zero_eq_sum_Icc]
  simp_rw [Finset.mul_sum]
  rw [mul_sub, mul_add, mul_sub]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  push_cast
  rw [Real.log_div hNR.ne' (mul_pos haR hdR).ne',
    Real.log_div hNR.ne' (mul_pos hbR hdR).ne',
    Real.log_mul haR.ne' hdR.ne', Real.log_mul hbR.ne' hdR.ne']
  ring

/-- For positive `b, c`: `selbergOneFourHarmonicMain b c N / (log N)^4 → 1` as `N → ∞`. -/
theorem tendsto_selbergOneFourHarmonicMain_div_log_fourth_one
    {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      selbergOneFourHarmonicMain b c N / Real.log N ^ (4 : ℕ))
      atTop (𝓝 1) := by
  have hB := tendsto_log_sub_const_div_log_one (Real.log b)
  have hH := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have hM1 := tendsto_harmonicLogWindowMoment_one_natDiv_div_log_sq_half hc
  have hM2 := tendsto_harmonicLogWindowMoment_two_natDiv_div_log_cube_third hc
  have hM3 :=
    tendsto_harmonicLogWindowMoment_three_natDiv_div_log_fourth_quarter hc
  have hlim := ((((hB.pow 3).mul hH).sub
      (((hB.pow 2).mul hM1).const_mul 3)).add
      ((hB.mul hM2).const_mul 3)).sub hM3
  have hscaled := hlim.const_mul 4
  norm_num at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergOneFourHarmonicMain_eq_moments hb hNpos]
  field_simp [hlogN]

/-- For positive `a, b, c`: `selbergTwoThreeHarmonicMain a b c N / (log N)^4 → 3/2` as `N → ∞`. -/
theorem tendsto_selbergTwoThreeHarmonicMain_div_log_fourth_three_halves
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      selbergTwoThreeHarmonicMain a b c N / Real.log N ^ (4 : ℕ))
      atTop (𝓝 (3 / 2 : ℝ)) := by
  have hA := tendsto_log_sub_const_div_log_one (Real.log a)
  have hB := tendsto_log_sub_const_div_log_one (Real.log b)
  have hH := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have hM1 := tendsto_harmonicLogWindowMoment_one_natDiv_div_log_sq_half hc
  have hM2 := tendsto_harmonicLogWindowMoment_two_natDiv_div_log_cube_third hc
  have hM3 :=
    tendsto_harmonicLogWindowMoment_three_natDiv_div_log_fourth_quarter hc
  have hlim := ((((hA.mul (hB.pow 2)).mul hH).sub
      (((hB.pow 2).add ((hA.mul hB).const_mul 2)).mul hM1)).add
      ((hA.add (hB.const_mul 2)).mul hM2)).sub hM3
  have hscaled := hlim.const_mul 6
  norm_num at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergTwoThreeHarmonicMain_eq_moments ha hb hNpos]
  field_simp [hlogN]

end

end RHTower.Sieve
