import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Localization transports finite complex pairings

A weighted pairing has the unweighted limit multiplied by the value of the test at the first
row's concentration point. This does not require distinct concentration points.
-/

open Complex Filter Topology
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

theorem sq_finiteWeighted_real_pairing_le {ι : Type*}
    (s : Finset ι) (f h : ι → ℂ) (g : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (a * ∑ i ∈ s, g i * (f i * conj (h i)).re) ^ 2 ≤
      (a * ∑ i ∈ s, ‖f i‖ ^ 2 * g i ^ 2) * (a * ∑ i ∈ s, ‖h i‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i _ => by positivity) (fun i _ => by positivity)
  intro i hi
  have hre : |(f i * conj (h i)).re| ≤ ‖f i‖ * ‖h i‖ := by
    simpa only [norm_mul, norm_conj] using abs_re_le_norm (f i * conj (h i))
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hre
  rw [sq_abs, mul_pow] at hsq
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (a * g i))]

/-- Localization of one row transports an unweighted pairing limit to a weighted one.
No separation of the two localization points is required. -/
theorem tendsto_finiteWeighted_real_pairing
    {ι : ℕ → Type*} (s : ∀ n, Finset (ι n))
    (a : ℕ → ℝ) (f h : ∀ n, ι n → ℂ) (g : ∀ n, ι n → ℝ)
    {b L T : ℝ} (ha : ∀ n, 0 ≤ a n)
    (herr : Tendsto (fun n => a n * ∑ i ∈ s n, ‖f n i‖ ^ 2 * (g n i - b) ^ 2)
      atTop (nhds 0))
    (hmass : Tendsto (fun n => a n * ∑ i ∈ s n, ‖h n i‖ ^ 2) atTop (nhds L))
    (hpair : Tendsto (fun n => a n * ∑ i ∈ s n, (f n i * conj (h n i)).re)
      atTop (nhds T)) :
    Tendsto (fun n => a n * ∑ i ∈ s n, g n i * (f n i * conj (h n i)).re)
      atTop (nhds (b * T)) := by
  have hsq : Tendsto
      (fun n => (a n * ∑ i ∈ s n, (g n i - b) * (f n i * conj (h n i)).re) ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (fun n => sq_finiteWeighted_real_pairing_le (s n) (f n) (h n)
        (fun i => g n i - b) (ha n))
    simpa using herr.mul hmass
  have hzero : Tendsto
      (fun n => a n * ∑ i ∈ s n, (g n i - b) * (f n i * conj (h n i)).re)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Function.comp_def, Real.norm_eq_abs, Real.sqrt_sq_eq_abs, Real.sqrt_zero]
      using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hsum := hzero.add (hpair.const_mul b)
  simp only [zero_add] at hsum
  convert hsum using 1
  ext n
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end GaloisForLFunctions.HTGeometry
