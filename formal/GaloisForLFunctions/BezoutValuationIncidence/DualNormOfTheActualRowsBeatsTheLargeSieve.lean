import GaloisForLFunctions.BezoutValuationIncidence.CentredPrimeBlockBeatsTheLargeSieve
import GaloisForLFunctions.BezoutValuationIncidence.DualNormOfTheCrossScaleFunctional

/-!
# The dual norm of the actual rows beats the large sieve

The cross-scale problem for arbitrary bounded small-scale coefficients is exactly the single-modulus
dual norm `Σ_{p ∈ S} |Λ_p(c')|/p`, `Λ_p` the kernel statistic: the sign pattern
`c(p) = sign Λ_p(c')` attains it up to the main term and the fourth-order error
(`exists_rowBilinear_sub_main_ge`). Bounding the cross-scale remainder of every bounded row on `S`
therefore bounds the dual norm. With the Möbius block and the centred prime block this gives, for
every `ε > 0` and all large `Q`, for every set `S` of primes `p ≤ Q₀` above the respective thresholds
(`8 log₂ Q ≤ ε² p`, resp. `8⌈(2Q)^α⌉(log 2Q + 1)² ≤ ε² p`),

`Σ_{p ∈ S} |Λ_p(c')|/p ≤ ε √(Σ_{p ∈ S} p²) √(Q + 2Q₀²) Q^{-3/2} + (1/6 + π²/72) |S'| Σ_{p ∈ S} 1/p
  + ¾ (Σ_{p ∈ S} p²) Σ_n |c'(n)|/n³ + 6 (Σ_{p ∈ S} p³) Σ_n |c'(n)|/n⁴`,

`S' = Σ_n c'(n)/n²` the block mass. The first term is `ε` times the large-sieve size, which coherent
rows attain; this is the bound on the single-modulus statistics of the actual Möbius and prime rows
at moduli growing with the window, from cancellation of the row in short windows (Matomäki–Radziwiłł,
Huxley) with no character or modulus average. Its power-saving form is the quasi-Riemann hypothesis
(`moebiusPowerWindowSaving_iff`, `primePowerWindowSaving_iff`).
-/

open Finset Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Bounded rows on a prime set -/

theorem sum_sq_mul_sq_le_of_abs_le_one {S : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) :
    ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2 ≤ ∑ p ∈ S, (p : ℝ) ^ 2 := by
  refine sum_le_sum fun p _ => ?_
  have : c p ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [hc p, abs_nonneg (c p)]
  nlinarith [sq_nonneg (p : ℝ)]

theorem sum_Icc_abs_mul_pow_le {N k : ℕ} {S : Finset ℕ} (hSN : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N)
    {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ∈ S) :
    ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ k ≤ ∑ p ∈ S, (p : ℝ) ^ k := by
  have hsub : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr (hSN p hp)
  rw [← sum_subset hsub fun d _ hd => by
    have : c d = 0 := by by_contra h; exact hd (hsupp d h)
    simp [this]]
  exact sum_le_sum fun p _ => by
    have := hc p
    have : (0 : ℝ) ≤ (p : ℝ) ^ k := by positivity
    nlinarith [abs_nonneg (c p)]

theorem sum_abs_div_le_of_abs_le_one {S : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) :
    ∑ p ∈ S, |c p| / p ≤ ∑ p ∈ S, 1 / (p : ℝ) :=
  sum_le_sum fun p _ => div_le_div_of_nonneg_right (hc p) (Nat.cast_nonneg _)

/-- The main term of a bounded row on primes: `|main(c)| ≤ (π²/72) |S'| Σ_{p ∈ S} 1/p`. -/
theorem abs_equidistributedMain_le {N : ℕ} {S : Finset ℕ} (hSN : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N)
    {c c' : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ∈ S) :
    |equidistributedMain N c c'| ≤
      Real.pi ^ 2 / 72 * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2| * ∑ p ∈ S, 1 / (p : ℝ) := by
  have hsub : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr (hSN p hp)
  rw [equidistributedMain, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi ^ 2 / 72)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← sum_subset hsub fun d _ hd => by
    have : c d = 0 := by by_contra h; exact hd (hsupp d h)
    simp [this]]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hSN p hp).1
  have hp0 : (0 : ℝ) < p := by linarith
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 3),
    abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 1), div_le_div_iff₀ (by positivity) hp0]
  have := hc p
  have h2 : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
  calc |c p| * ((p : ℝ) ^ 2 - 1) * p ≤ 1 * ((p : ℝ) ^ 2 - 1) * p := by gcongr
    _ ≤ 1 * (p : ℝ) ^ 3 := by nlinarith

/-- **Dual norm from remainder bounds.** If every row `|c| ≤ 1` on `S` has cross-scale remainder at
most `ε V Σ₂(c)^{1/2} + m Σ_p |c(p)|/p + ¾ Σ_d |c(d)| d² T₃`, then
`Σ_{p ∈ S} |Λ_p(c')|/p ≤ ε V (Σ p²)^{1/2} + (m + (π²/72)|S'|) Σ 1/p + ¾ (Σ p²) T₃ + 6 (Σ p³) T₄`. -/
theorem sum_abs_kernelStatistic_le_of_remainder {N : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) {c' : ℕ → ℝ} {ε V m : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hm : 0 ≤ m)
    (hrem : ∀ c : ℕ → ℝ, (∀ d, |c d| ≤ 1) → (∀ d, c d ≠ 0 → d ∈ S) →
      |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c'| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * V + m * ∑ p ∈ S, |c p| / p +
          3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3) :
    ∑ p ∈ S, |kernelStatistic N c' p| / p ≤
      ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) * V +
        (m + Real.pi ^ 2 / 72 * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2|) * ∑ p ∈ S, 1 / (p : ℝ) +
        3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 +
        6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  obtain ⟨c, hc, hsupp, hge⟩ := exists_rowBilinear_sub_main_ge N hS c'
  have hSN : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N := fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2⟩
  have h1 := hrem c hc hsupp
  have h2 := abs_equidistributedMain_le hSN (c' := c') hc hsupp
  have h3 : Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) ≤ Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt (sum_sq_mul_sq_le_of_abs_le_one hc)
  have h4 := sum_abs_div_le_of_abs_le_one (S := S) hc
  have h5 := sum_Icc_abs_mul_pow_le (k := 2) hSN hc hsupp
  have hT3 : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := sum_nonneg fun _ _ => by positivity
  have hrem' : |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c'| ≤
      ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) * V + m * ∑ p ∈ S, 1 / (p : ℝ) +
        3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
    refine h1.trans (add_le_add (add_le_add ?_ ?_) ?_)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hε) hV
    · exact mul_le_mul_of_nonneg_left h4 hm
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by norm_num)) hT3
  have habs := le_abs_self (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c')
  have hmain := neg_abs_le (equidistributedMain N c c')
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
