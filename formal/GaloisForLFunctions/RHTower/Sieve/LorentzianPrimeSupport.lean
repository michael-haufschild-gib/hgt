import GaloisForLFunctions.RHTower.Sieve.LorentzianMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PrimeLogWindowCount

/-!
# The Lorentzian mean square of a prime-supported Dirichlet polynomial

The neighbour count of the almost-diagonal mean value theorem only ever sees indices carrying a nonzero
coefficient: dropping the vanishing terms from the polynomial replaces the count over the index set by
the count over the **support**.  For coefficients supported on primes the support count is a
short-interval prime count, and the Selberg sieve discharges it:

`∫_ℝ ‖∑_{p} a_p p^{2πiw}‖² dw/(1+w²)
   ≤ (25π/2) ∑_p (2(p(e^δ - e^{-δ}) + 1)/log Y + selbergFibreError z Y + z) ‖a_p‖²`,   `δ = 1/(2π)`.

This is GHS Lemma 1 over the whole frequency line: a mean square of a prime-supported Dirichlet
polynomial weighted by `Λ(n)/n` rather than `Λ(n)²/n`, with no truncation of the line and no parameter
except the sieve level.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Set Finset

/-- Dropping the vanishing coefficients does not change the polynomial. -/
theorem logPoly_eq_logPoly_filter (a : ℕ → ℂ) (s : Finset ℕ) (w : ℝ) :
    logPoly a s w = logPoly a {n ∈ s | a n ≠ 0} w := by
  classical
  rw [logPoly, logPoly]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnot => ?_).symm
  rw [Finset.mem_filter, not_and] at hnot
  have hz : a n = 0 := by
    by_contra hne
    exact (hnot hn) hne
  rw [hz, zero_mul]

/-- **The Lorentzian mean value theorem against the support count.** -/
theorem integral_lorentz_normSq_logPoly_le_support_count (a : ℕ → ℂ) (s : Finset ℕ) :
    (∫ w : ℝ, ‖logPoly a s w‖ ^ 2 / (1 + w ^ 2))
      ≤ (25 * Real.pi / 2)
          * ∑ n ∈ {n ∈ s | a n ≠ 0},
              (logNeighbourCount {n ∈ s | a n ≠ 0} (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ 2 := by
  classical
  have hcongr : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 / (1 + w ^ 2)
      = ‖logPoly a {n ∈ s | a n ≠ 0} w‖ ^ 2 / (1 + w ^ 2) := by
    intro w
    rw [logPoly_eq_logPoly_filter a s w]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  exact integral_lorentz_normSq_logPoly_le_count a {n ∈ s | a n ≠ 0}

/-- **GHS Lemma 1 over the whole frequency line.**  For coefficients supported on primes the support
count of the Lorentzian mean value theorem is a short-interval prime count, discharged by the Selberg
sieve at any admissible level. -/
theorem integral_lorentz_normSq_logPoly_le_prime_sieve (a : ℕ → ℂ) (s : Finset ℕ)
    (hsupp : ∀ n ∈ s, a n ≠ 0 → n.Prime) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    (∫ w : ℝ, ‖logPoly a s w‖ ^ 2 / (1 + w ^ 2))
      ≤ (25 * Real.pi / 2) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
              / Real.log Y
            + selbergFibreError z Y + (z : ℝ)) * ‖a n‖ ^ 2 := by
  classical
  set s' : Finset ℕ := {n ∈ s | a n ≠ 0} with hs'def
  have hprime : ∀ m ∈ s', m.Prime := by
    intro m hm
    rw [hs'def, Finset.mem_filter] at hm
    exact hsupp m hm.1 hm.2
  have hδ : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hbound : ∀ n ∈ s',
      (logNeighbourCount s' (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ 2
        ≤ (2 * ((n : ℝ) * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
              / Real.log Y
            + selbergFibreError z Y + (z : ℝ)) * ‖a n‖ ^ 2 := by
    intro n hn
    have hn1 : 1 ≤ n := (hprime n hn).one_lt.le.trans' (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (logNeighbourCount_le_sieve s' hprime hδ hn1 z Y hY hYz hz hlog) (by positivity)
  have hsub : s' ⊆ s := by
    rw [hs'def]
    exact Finset.filter_subset _ _
  have hnn : ∀ n ∈ s, n ∉ s' →
      0 ≤ (2 * ((n : ℝ) * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
              / Real.log Y
            + selbergFibreError z Y + (z : ℝ)) * ‖a n‖ ^ 2 := by
    intro n hn hnot
    have hzero : a n = 0 := by
      by_contra hne
      exact hnot (by rw [hs'def, Finset.mem_filter]; exact ⟨hn, hne⟩)
    rw [hzero]
    simp
  refine le_trans (integral_lorentz_normSq_logPoly_le_support_count a s) ?_
  rw [← hs'def]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (Finset.sum_le_sum hbound) (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)

end RHTower.Sieve

end
