import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerHarmonicGeneral

/-!
# The harmonic main term of the gcd-logarithmic Selberg family

Peeling the gcd out of `log (m,n)` replaces the reciprocal diagonal weight `1/d` of the principal
Selberg collapse by `log d / d`.  The resulting harmonic model is evaluated here at every pair of
logarithmic powers:

`selbergGcdLogHarmonicMain q r a b N / (log N)^{q+r+2} → (q+1)(r+1)/((q+r+1)(q+r+2))`,

i.e. with `i = q+1`, `j = r+1` the leading constant is `i·j/((i+j-1)(i+j))`.  The proof is the
identity `log d = (log N - log a) - log (N/(a d))`, which converts the model into the two ordinary
harmonic mains of `SelbergLogPowerHarmonicGeneral` at consecutive degrees.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Harmonic model for the gcd-logarithmic Selberg family. -/
def selbergGcdLogHarmonicMain (q r a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * Real.log (d : ℝ) *
      Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
      Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r) / (d : ℝ)

/-- Exact conversion into two ordinary harmonic mains at consecutive degrees. -/
theorem selbergGcdLogHarmonicMain_eq
    (q r : ℕ) {a b N : ℕ} (ha : 0 < a) (hN : 0 < N) :
    selbergGcdLogHarmonicMain q r a b N =
      (Real.log (N : ℝ) - Real.log (a : ℝ)) *
          selbergLogPowerHarmonicMain q r a b N -
        (((q : ℝ) + 1) / ((q : ℝ) + 2)) *
          selbergLogPowerHarmonicMain (q + 1) r a b N := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [selbergGcdLogHarmonicMain, selbergLogPowerHarmonicMain,
    selbergLogPowerHarmonicMain, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hlogd : Real.log (d : ℝ) =
      (Real.log (N : ℝ) - Real.log (a : ℝ)) -
        Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) := by
    push_cast
    rw [Real.log_div hNR.ne' (by positivity), Real.log_mul haR.ne' hdR.ne']
    ring
  rw [hlogd]
  have hq2 : ((q : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The gcd-logarithmic harmonic main term at every pair of logarithmic powers.** -/
theorem tendsto_selbergGcdLogHarmonicMain_div_log_pow
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergGcdLogHarmonicMain q r a b N / Real.log N ^ (q + r + 2))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)))) := by
  have hbase := tendsto_selbergLogPowerHarmonicMain_div_log_pow q r ha hb
  have hnext := tendsto_selbergLogPowerHarmonicMain_div_log_pow (q + 1) r ha hb
  push_cast at hnext
  have hshift := tendsto_log_sub_const_div_log_one (Real.log (a : ℝ))
  have hfirst : Tendsto (fun N : ℕ =>
      ((Real.log (N : ℝ) - Real.log (a : ℝ)) / Real.log (N : ℝ)) *
        (selbergLogPowerHarmonicMain q r a b N / Real.log N ^ (q + r + 1)))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1))) := by
    simpa using hshift.mul hbase
  have hsecond : Tendsto (fun N : ℕ =>
      (((q : ℝ) + 1) / ((q : ℝ) + 2)) *
        (selbergLogPowerHarmonicMain (q + 1) r a b N /
          Real.log N ^ (q + 1 + r + 1)))
      atTop (𝓝 ((((q : ℝ) + 1) / ((q : ℝ) + 2)) *
        (((((q : ℕ) : ℝ) + 1 + 1) * ((r : ℝ) + 1)) /
          ((((q : ℕ) : ℝ) + 1) + (r : ℝ) + 1)))) := by
    have h := hnext.const_mul (((q : ℝ) + 1) / ((q : ℝ) + 2))
    refine h.congr' ?_
    filter_upwards with N
    norm_num
  have hsub := hfirst.sub hsecond
  have hval : (((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1) -
      (((q : ℝ) + 1) / ((q : ℝ) + 2)) *
        (((((q : ℝ) + 1) + 1) * ((r : ℝ) + 1)) /
          (((q : ℝ) + 1) + (r : ℝ) + 1)) =
      (((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)) := by
    have h1 : ((q : ℝ) + (r : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((q : ℝ) + (r : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((q : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [hval] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergGcdLogHarmonicMain_eq q r ha hNpos]
  have hexp : q + 1 + r + 1 = q + r + 2 := by omega
  rw [hexp]
  have hpow : Real.log (N : ℝ) ^ (q + r + 2) =
      Real.log (N : ℝ) * Real.log (N : ℝ) ^ (q + r + 1) := by
    rw [show q + r + 2 = (q + r + 1) + 1 by omega, pow_succ]
    ring
  rw [sub_div, hpow]
  field_simp

end

end RHTower.Sieve
