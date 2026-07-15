import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Transfer from pointwise harmonic asymptotics to logarithmic residues
-/

open Filter Topology Finset Asymptotics

namespace GaloisForLFunctions

noncomputable section

theorem tendsto_harmonic_cast_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n => log_add_one_le_harmonic n) hlog

/-- If `e_n → 0`, then its harmonic weighted partial sums are `o(log N)`. -/
theorem tendsto_harmonicWeighted_error_zero {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, e n / ((n : ℝ) + 1)) / Real.log N)
      atTop (nhds 0) := by
  have heo : (fun n : ℕ => e n / ((n : ℝ) + 1)) =o[atTop]
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    apply (isLittleO_iff_tendsto (fun n hzero => by
      exfalso
      exact (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne' hzero)).2
    refine he.congr' ?_
    filter_upwards with n
    field_simp
  have hweight : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)) atTop atTop := by
    simpa [harmonic] using tendsto_harmonic_cast_atTop
  have hsum := heo.sum_range (fun n => by positivity) hweight
  have hratio : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, e n / ((n : ℝ) + 1)) /
        (∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1))) atTop (nhds 0) :=
    hsum.tendsto_div_nhds_zero
  have hratio' : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, e n / ((n : ℝ) + 1)) / (harmonic N : ℝ))
      atTop (nhds 0) := by
    simpa [harmonic] using hratio
  have hproduct := hratio'.mul tendsto_harmonic_div_log
  simpa only [zero_mul] using hproduct.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hharm : (harmonic N : ℝ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : N ≠ 0)).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp)

/-- A pointwise coefficient law `(n+1)a_n → R` forces the exact logarithmic residue
`(1/log N)∑_{n<N}a_n → R`. -/
theorem tendsto_logResidue_of_mul_succ_tendsto
    {a : ℕ → ℝ} {R : ℝ}
    (ha : Tendsto (fun n : ℕ => a n * ((n : ℝ) + 1)) atTop (nhds R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / Real.log N)
      atTop (nhds R) := by
  have he : Tendsto (fun n : ℕ => a n * ((n : ℝ) + 1) - R) atTop (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr ha
  have herror := tendsto_harmonicWeighted_error_zero he
  have hmain := tendsto_harmonic_div_log.const_mul R
  have htotal := hmain.add herror
  have heq : ∀ᶠ N : ℕ in atTop,
      R * ((harmonic N : ℝ) / Real.log N) +
          (∑ n ∈ Finset.range N, (a n * ((n : ℝ) + 1) - R) / ((n : ℝ) + 1)) /
            Real.log N =
        (∑ n ∈ Finset.range N, a n) / Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    rw [← mul_div_assoc, ← add_div]
    congr 1
    have hharm : (harmonic N : ℝ) =
        ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [harmonic]
      push_cast
      simp only [one_div]
    rw [hharm, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    field_simp
    ring
  simpa only [mul_one, add_zero] using htotal.congr' heq

end

end GaloisForLFunctions
