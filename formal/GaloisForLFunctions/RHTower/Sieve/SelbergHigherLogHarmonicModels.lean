import GaloisForLFunctions.RHTower.Sieve.HarmonicLogMomentAsymptotics

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

theorem harmonicLogWindowMoment_zero_eq_sum_Icc (m N : ℕ) :
    harmonicLogWindowMoment m 0 N =
      ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) ^ m / (d : ℝ) := by
  rw [harmonicLogWindowMoment]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro d hd
    rfl

/-- Harmonic main term for the principal `(log, log²)` model. -/
def selbergMixedHarmonicMain (b c N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / c),
    2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) / (d : ℝ)

/-- Harmonic main term for the principal `(log², log²)` model. -/
def selbergQuadraticHarmonicMain (a b c N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / c),
    4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
      Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) / (d : ℝ)

theorem selbergMixedHarmonicMain_eq_moments
    {b c N : ℕ} (hb : 0 < b) (hN : 0 < N) :
    selbergMixedHarmonicMain b c N =
      2 * (Real.log N - Real.log b) * (harmonic (N / c) : ℝ) -
        2 * harmonicLogWindowMoment 1 0 (N / c) := by
  rw [selbergMixedHarmonicMain, ← sum_Icc_one_div_eq_harmonic,
    harmonicLogWindowMoment_zero_eq_sum_Icc]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  push_cast
  rw [Real.log_div hNR.ne' (mul_pos hbR hdR).ne', Real.log_mul hbR.ne' hdR.ne']
  ring

theorem selbergQuadraticHarmonicMain_eq_moments
    {a b c N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    selbergQuadraticHarmonicMain a b c N =
      4 * ((Real.log N - Real.log a) * (Real.log N - Real.log b) *
          (harmonic (N / c) : ℝ) -
        ((Real.log N - Real.log a) + (Real.log N - Real.log b)) *
          harmonicLogWindowMoment 1 0 (N / c) +
        harmonicLogWindowMoment 2 0 (N / c)) := by
  rw [selbergQuadraticHarmonicMain, ← sum_Icc_one_div_eq_harmonic,
    harmonicLogWindowMoment_zero_eq_sum_Icc,
    harmonicLogWindowMoment_zero_eq_sum_Icc]
  rw [mul_add, mul_sub]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
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

theorem tendsto_log_sub_const_div_log_one (K : ℝ) :
    Tendsto (fun N : ℕ => (Real.log N - K) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => K / Real.log N) atTop (𝓝 0) :=
    hlog.const_div_atTop K
  have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hsmall
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlogN]

/-- Every fixed `(log, log²)` harmonic dilation has leading coefficient one. -/
theorem tendsto_selbergMixedHarmonicMain_div_log_sq_one
    {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℕ => selbergMixedHarmonicMain b c N / Real.log N ^ (2 : ℕ))
      atTop (𝓝 1) := by
  have hB := tendsto_log_sub_const_div_log_one (Real.log b)
  have hH := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have hM := tendsto_harmonicLogWindowMoment_one_natDiv_div_log_sq_half hc
  have hlim := ((hB.mul hH).const_mul 2).sub (hM.const_mul 2)
  norm_num at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergMixedHarmonicMain_eq_moments hb hNpos]
  field_simp [hlogN]

/-- Every fixed `(log², log²)` harmonic dilation has leading coefficient `4/3`. -/
theorem tendsto_selbergQuadraticHarmonicMain_div_log_cube_four_thirds
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      selbergQuadraticHarmonicMain a b c N / Real.log N ^ (3 : ℕ))
      atTop (𝓝 (4 / 3 : ℝ)) := by
  have hA := tendsto_log_sub_const_div_log_one (Real.log a)
  have hB := tendsto_log_sub_const_div_log_one (Real.log b)
  have hH := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have hM1 := tendsto_harmonicLogWindowMoment_one_natDiv_div_log_sq_half hc
  have hM2 := tendsto_harmonicLogWindowMoment_two_natDiv_div_log_cube_third hc
  have hlim := (((hA.mul hB).mul hH).sub ((hA.add hB).mul hM1)).add hM2
  have hscaled := hlim.const_mul 4
  norm_num at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergQuadraticHarmonicMain_eq_moments ha hb hNpos]
  field_simp [hlogN]

end

end RHTower.Sieve
