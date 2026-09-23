import GaloisForLFunctions.RHTower.Sieve.HuxleyLargeValues
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Halász--Montgomery for a dyadic Dirichlet row

Composing the two-regime Gram-row estimate with the duality principle gives the mean-square bound
at separated frequencies without any absorption hypothesis:

`∑_r |⟪φ_r, a⟫|² ≤ (N + (12πN/δ)(1 + log K) + K·B)·‖a‖²`,

where `B` is the second-derivative envelope of the block on the frequency window.  The first two
terms are the diagonal and the Kuzmin--Landau kernel; the third is the price of the resonant
frequencies, and is what makes the estimate useful precisely when the frequency set is sparse.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Halász--Montgomery at separated frequencies, dyadic block, unconditional.** -/
theorem halaszMontgomery_dyadic {N K : ℕ} (hN : 1 ≤ N) (a : EuclideanSpace ℂ (Fin N))
    {lam : ℕ → ℝ} {delta U T B : ℝ} (hdelta : 0 < delta) (hU : 0 < U)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ Finset.range K, ∀ s ∈ Finset.range K, |lam s - lam r| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B) :
    ∑ r ∈ Finset.range K, ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
            * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (K : ℝ) * B) * ‖a‖ ^ (2 : ℕ) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (by norm_num) hB1
  have hharm : (0 : ℝ) ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hΔ0 : (0 : ℝ) ≤ (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
      * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) + (K : ℝ) * B := by
    have h1 : (0 : ℝ) ≤ (12 * Real.pi * (N : ℝ) / delta)
        * ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) ≤ (K : ℝ) * B := by positivity
    linarith
  refine sum_norm_inner_sq_le_of_schur (Finset.range K)
    (fun r => dyadicDirRow N (lam r)) hΔ0 ?_ a
  intro r hr
  exact sum_norm_inner_dyadicDirRow_le_huxley hN hdelta hgap hdiam hU hnear hlamT hB hB1
    (Finset.mem_range.1 hr)

/-- **Halász--Montgomery in closed logarithmic form.** -/
theorem halaszMontgomery_dyadic_log {N K : ℕ} (hN : 1 ≤ N) (a : EuclideanSpace ℂ (Fin N))
    {lam : ℕ → ℝ} {delta U T B : ℝ} (hdelta : 0 < delta) (hU : 0 < U)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ Finset.range K, ∀ s ∈ Finset.range K, |lam s - lam r| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hB : logDyadicSecondEnvelope N U T ≤ B) (hB1 : 1 ≤ B) :
    ∑ r ∈ Finset.range K, ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log K)
            + (K : ℝ) * B) * ‖a‖ ^ (2 : ℕ) := by
  refine le_trans (halaszMontgomery_dyadic hN a hdelta hU hgap hdiam hnear hlamT hB hB1) ?_
  have hharm : ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log K := by
    rw [← sum_Icc_one_div_eq_sum_range]
    exact sum_Icc_one_div_le_one_add_log K
  have hcoef : (0 : ℝ) ≤ 12 * Real.pi * (N : ℝ) / delta := by positivity
  have hstep := mul_le_mul_of_nonneg_left hharm hcoef
  have hnorm : (0 : ℝ) ≤ ‖a‖ ^ (2 : ℕ) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hnorm
  linarith

end RHTower.Sieve
