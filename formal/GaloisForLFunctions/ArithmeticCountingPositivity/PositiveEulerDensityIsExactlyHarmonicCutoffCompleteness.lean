import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasItsEulerProductHarmonicMean

/-!
# Positive Euler density is exactly harmonic cutoff completeness

The density factors into a finite head and an arbitrary residual prime
pattern. The exact squared cutoff error is twice the residual harmonic
defect. Its limit distinguishes positive Euler density, where finite prime
cutoffs approximate the whole sign, from zero density, where every fixed
cutoff has limiting squared distance two.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open private primeSetCutoff_tail primeSetCutoff_mono from
  GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasItsEulerProductHarmonicMean
open private primeSetCutoff_prime primeSetFlip_partition primeSetFlip_cutoff_eq
  primeSetFlip_mul_self from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips

/-- Squared harmonic distance from a prime pattern to its finite prime cutoff. -/
def primeSetCutoffDistanceSq (P : Set ℕ) (Q N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 / n) /
    gaugeHarmonicSum (fun _ => 1) N

/-- Prime cutoffs beyond the integer horizon have exactly zero harmonic error. -/
theorem primeSetCutoffDistanceSq_eq_zero_of_le (P : Set ℕ) {Q N : ℕ} (hNQ : N ≤ Q) :
    primeSetCutoffDistanceSq P Q N = 0 := by
  have hz : (∑ n ∈ Icc 1 N,
      (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 / n) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [primeSetFlip_eq_finiteFlip_of_le P ((mem_Icc.mp hn).2.trans hNQ),
      sub_self, pow_two, zero_mul, zero_div]
  rw [primeSetCutoffDistanceSq, hz, zero_div]

/-- Removing a finite prime head divides the full Euler density by its
strictly positive finite density. -/
theorem primeSetHarmonicDensity_tail (P : Set ℕ) (Q : ℕ) :
    primeSetHarmonicDensity (P \ Set.Iic Q) =
      primeSetHarmonicDensity P / finiteFlipHarmonicDensity (primeSetCutoff P Q) := by
  have hprod := (tendsto_primeSetCutoff_density (P \ Set.Iic Q)).mul_const
    (finiteFlipHarmonicDensity (primeSetCutoff P Q))
  have hevent : ∀ᶠ N : ℕ in atTop,
      finiteFlipHarmonicDensity (primeSetCutoff (P \ Set.Iic Q) N) *
        finiteFlipHarmonicDensity (primeSetCutoff P Q) =
          finiteFlipHarmonicDensity (primeSetCutoff P N) := by
    filter_upwards [eventually_ge_atTop Q] with N hN
    rw [primeSetCutoff_tail]
    exact prod_sdiff (primeSetCutoff_mono P hN)
  have he := tendsto_nhds_unique (hprod.congr' hevent) (tendsto_primeSetCutoff_density P)
  exact (eq_div_iff (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).ne').mpr he

/-- The exact squared cutoff error is twice the residual harmonic defect. -/
theorem primeSetFlip_cutoff_distance_sq_eq (P : Set ℕ) (Q : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    primeSetCutoffDistanceSq P Q N =
      2 * (1 - harmonicCorrelation (primeSetFlip (P \ Set.Iic Q)) N) := by
  have he (n : ℕ) :
      (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 =
        2 * (1 - primeSetFlip (P \ Set.Iic Q) n) := by
    rw [← primeSetFlip_cutoff_eq P Q n, primeSetFlip_partition P Q n]
    have hu : primeSetFlip (P ∩ Set.Iic Q) n ^ 2 = 1 := by
      simpa only [pow_two] using primeSetFlip_mul_self (P ∩ Set.Iic Q) n
    have hv : primeSetFlip (P \ Set.Iic Q) n ^ 2 = 1 := by
      simpa only [pow_two] using primeSetFlip_mul_self (P \ Set.Iic Q) n
    calc
      _ = primeSetFlip (P ∩ Set.Iic Q) n ^ 2 *
          (primeSetFlip (P \ Set.Iic Q) n ^ 2 - 2 * primeSetFlip (P \ Set.Iic Q) n + 1) := by ring
      _ = _ := by rw [hu, hv]; ring
  have hsum : (∑ n ∈ Icc 1 N,
      (primeSetFlip P n - finiteFlip (primeSetCutoff P Q) n) ^ 2 / n) =
        2 * (gaugeHarmonicSum (fun _ => 1) N -
          gaugeHarmonicSum (primeSetFlip (P \ Set.Iic Q)) N) := by
    rw [gaugeHarmonicSum, gaugeHarmonicSum, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n _
    rw [he]
    ring
  rw [primeSetCutoffDistanceSq, hsum, harmonicCorrelation]
  field_simp [(gaugeHarmonicSum_one_pos hN).ne']

/-- The exact limiting squared harmonic distance to a fixed prime cutoff. -/
theorem primeSetFlip_cutoff_distance_sq_tendsto (P : Set ℕ) (Q : ℕ) :
    Tendsto (primeSetCutoffDistanceSq P Q) atTop
      (𝓝 (2 * (1 - primeSetHarmonicDensity P /
        finiteFlipHarmonicDensity (primeSetCutoff P Q)))) := by
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hOne.sub (primeSetFlip_harmonicCorrelation_tendsto (P \ Set.Iic Q))).const_mul 2
  rw [primeSetHarmonicDensity_tail] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (primeSetFlip_cutoff_distance_sq_eq P Q hN).symm

/-- Finite prime cutoffs approximate the full sign in eventual harmonic
mean square exactly when the Euler-product density is positive. -/
theorem primeSetFlip_harmonic_cutoffs_complete_iff (P : Set ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
      ∀ᶠ N : ℕ in atTop, primeSetCutoffDistanceSq P Q N < ε) ↔
        0 < primeSetHarmonicDensity P := by
  constructor
  · intro hcomplete
    by_contra hn
    have hz : primeSetHarmonicDensity P = 0 :=
      le_antisymm (le_of_not_gt hn) (primeSetHarmonicDensity_bounds P).1
    obtain ⟨Q, hQ⟩ := hcomplete 1 zero_lt_one
    have hsmall := hQ Q le_rfl
    have hlim : Tendsto (primeSetCutoffDistanceSq P Q) atTop (𝓝 (2 : ℝ)) := by
      simpa only [hz, zero_div, sub_zero, mul_one] using primeSetFlip_cutoff_distance_sq_tendsto P Q
    have hbad : (2 : ℝ) ≤ 1 := le_of_tendsto hlim (hsmall.mono fun _ h => h.le)
    norm_num at hbad
  · intro hc ε hε
    have hconst : Tendsto (fun _ : ℕ => primeSetHarmonicDensity P) atTop
        (𝓝 (primeSetHarmonicDensity P)) := tendsto_const_nhds
    have hratio := hconst.div (tendsto_primeSetCutoff_density P) hc.ne'
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have houter : Tendsto (fun Q => 2 * (1 - primeSetHarmonicDensity P /
        finiteFlipHarmonicDensity (primeSetCutoff P Q))) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Pi.div_apply, div_self hc.ne', sub_self, mul_zero] using (hOne.sub hratio).const_mul 2
    obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp (houter.eventually_lt_const hε)
    exact ⟨Q₀, fun Q hQ =>
      (primeSetFlip_cutoff_distance_sq_tendsto P Q).eventually_lt_const (hQ₀ Q hQ)⟩

end GaloisForLFunctions.ArithmeticCountingPositivity
