import GaloisForLFunctions.RHTower.SuzukiEndpointPrimeRegularCancellation

/-!
# Global disposal of the endpoint Binet error

The endpoint-scale identity leaves a Laplace main term plus an explicit Binet error per literal
prime atom.  This module proves that the error aggregates against the actual finite von-Mangoldt
source with no source splitting: its only cost is the literal total von-Mangoldt mass.  The
surviving Laplace codiagonal is intentionally not estimated here.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Finite actual-source aggregation of the endpoint Binet error.  Every coefficient remains
the literal von-Mangoldt coefficient; no unsigned proxy replaces the Laplace main term. -/
theorem abs_sum_endpoint_prime_regular_sub_laplace_le
    {N : ℕ} (s : Finset ℕ) {q L T : ℝ} (hN : 0 < N) (hT : 0 < T)
    (hqL : q ≤ 2 * L) (hTq : T ≤ Real.log (N : ℝ) - q) :
    |(∑ k ∈ s,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q)) -
      ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
      (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) *
        (Real.exp (-3 * Real.log (N : ℝ) + 5 * L) /
          (1 - Real.exp (-2 * T))) := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ s,
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q) -
          ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2))| ≤
      ∑ k ∈ s,
        |(ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q) -
          ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k *
        (Real.exp (-3 * Real.log (N : ℝ) + 5 * L) /
          (1 - Real.exp (-2 * T))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_endpoint_prime_regular_sub_laplace_le hN hT hqL hTq
    _ = _ := by rw [← Finset.sum_mul]

/-- Elementary source-only mass cap for any finite positive portion of an aperture. -/
theorem sum_vonMangoldt_le_card_mul_log_of_pos_le
    {N : ℕ} (s : Finset ℕ) (_hN : 0 < N)
    (hs : ∀ k ∈ s, 0 < k ∧ k ≤ N) :
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤
      (s.card : ℝ) * Real.log (N : ℝ) := by
  calc
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤
        ∑ k ∈ s, Real.log (k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact ArithmeticFunction.vonMangoldt_le_log
    _ ≤ ∑ _k ∈ s, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := (hs k hk).2
      exact Real.log_le_log (by exact_mod_cast (hs k hk).1) (by exact_mod_cast hkN)
    _ = _ := by simp

end

end GaloisForLFunctions.RHTower
