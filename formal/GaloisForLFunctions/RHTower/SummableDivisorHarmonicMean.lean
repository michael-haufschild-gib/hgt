import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import GaloisForLFunctions.HTGeometry.HarmonicLogFourierMode
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Harmonic numbers are monotone after casting to `ℝ`. -/
theorem harmonic_cast_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  have hq : harmonic m ≤ harmonic n := by
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hmn ih =>
        rw [harmonic_succ]
        exact ih.trans (le_add_of_nonneg_right
          (inv_nonneg.mpr (show (0 : ℚ) ≤ (n + 1 : ℕ) by positivity)))
  exact_mod_cast hq

/-- A fixed divisor does not alter the leading harmonic logarithmic ratio. -/
theorem tendsto_harmonic_natDiv_div_log {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (harmonic (N / d) : ℝ) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror : Tendsto
      (fun N : ℕ => ((harmonic (N / d) : ℝ) - Real.log N) / Real.log N)
      atTop (𝓝 0) :=
    (GaloisForLFunctions.HTGeometry.tendsto_harmonic_natDiv_sub_log hd).div_atTop hlog
  have hadd := herror.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  simpa only [zero_add] using hadd.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogne : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
    ring)

/-- Finite harmonic cutoff written as an infinite series with finite support. -/
noncomputable def summableDivisorHarmonicTerm (g : ℕ → ℝ) (N d : ℕ) : ℝ :=
  if d ∈ Finset.Icc 1 N then
    g d * ((harmonic (N / d) : ℝ) / Real.log N)
  else 0

theorem tendsto_summableDivisorHarmonicTerm (g : ℕ → ℝ) (hg0 : g 0 = 0) (d : ℕ) :
    Tendsto (fun N : ℕ => summableDivisorHarmonicTerm g N d) atTop (𝓝 (g d)) := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp [summableDivisorHarmonicTerm, hg0]
  · have hmain := (tendsto_harmonic_natDiv_div_log hd).const_mul (g d)
    simpa only [mul_one] using hmain.congr' (by
      filter_upwards [eventually_ge_atTop d] with N hNd
      rw [summableDivisorHarmonicTerm, if_pos]
      exact Finset.mem_Icc.mpr ⟨hd, hNd⟩)

theorem eventually_norm_summableDivisorHarmonicTerm_le (g : ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      ‖summableDivisorHarmonicTerm g N d‖ ≤ 2 * |g d| := by
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN d
  rw [summableDivisorHarmonicTerm]
  split_ifs with hd
  · have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    have hharmonic : (0 : ℝ) ≤ (harmonic (N / d) : ℝ) := by
      simpa using harmonic_cast_mono (m := 0) (n := N / d) (Nat.zero_le _)
    have hmono : (harmonic (N / d) : ℝ) ≤ (harmonic N : ℝ) :=
      harmonic_cast_mono (Nat.div_le_self N d)
    have hfull_nonneg : 0 ≤ (harmonic N : ℝ) / Real.log N :=
      div_nonneg (by
        simpa using harmonic_cast_mono (m := 0) (n := N) (Nat.zero_le _)) hlogpos.le
    have hdec_nonneg : 0 ≤ (harmonic (N / d) : ℝ) / Real.log N :=
      div_nonneg hharmonic hlogpos.le
    have hdec_le : (harmonic (N / d) : ℝ) / Real.log N ≤
        (harmonic N : ℝ) / Real.log N :=
      div_le_div_of_nonneg_right hmono hlogpos.le
    have hfull_le_two : |(harmonic N : ℝ) / Real.log N| ≤ 2 := by
      rw [abs_of_nonneg hfull_nonneg]
      rw [Real.dist_eq] at hnearN
      have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
          |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdec_nonneg]
    have hdec_two : (harmonic (N / d) : ℝ) / Real.log N ≤ 2 := by
      exact hdec_le.trans (by simpa [abs_of_nonneg hfull_nonneg] using hfull_le_two)
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hdec_two (abs_nonneg (g d))
  · simp

theorem tsum_summableDivisorHarmonicTerm (g : ℕ → ℝ) (N : ℕ) :
    (∑' d : ℕ, summableDivisorHarmonicTerm g N d) =
      ∑ d ∈ Finset.Icc 1 N, g d * ((harmonic (N / d) : ℝ) / Real.log N) := by
  have hsupp : ∀ d ∉ Finset.Icc 1 N, summableDivisorHarmonicTerm g N d = 0 := by
    intro d hd
    simp [summableDivisorHarmonicTerm, hd]
  rw [tsum_eq_sum hsupp]
  apply Finset.sum_congr rfl
  intro d hd
  simp [summableDivisorHarmonicTerm, hd]

/-- Dominated harmonic divisor mean. Absolute summability of the reciprocal residue is enough for
the leading logarithmic coefficient; no logarithmic moment is required. -/
theorem tendsto_summableDivisorHarmonicMean (g : ℕ → ℝ) (hg0 : g 0 = 0)
    (hsum : Summable (fun d : ℕ => |g d|)) :
    Tendsto
      (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
        g d * ((harmonic (N / d) : ℝ) / Real.log N))
      atTop (𝓝 (∑' d : ℕ, g d)) := by
  have hbound : Summable (fun d : ℕ => 2 * |g d|) := hsum.mul_left 2
  have hdom := tendsto_tsum_of_dominated_convergence hbound
    (tendsto_summableDivisorHarmonicTerm g hg0)
    (eventually_norm_summableDivisorHarmonicTerm_le g)
  simpa only [tsum_summableDivisorHarmonicTerm] using hdom

end

end RHTower
