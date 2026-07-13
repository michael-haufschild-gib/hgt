import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSubpowerGate

/-!
# A completed-error finite-difference gate to RH

The dyadic weighted von Mangoldt inequality is exactly a one-sided local regularity statement for
the source-defined completed critical-Mellin error.  The exact identity leaves a positive
`O(n⁻¹ᐟ²)` endpoint value.  Since this value is bounded by a fixed multiple of every positive
power of `n`, even the endpoint-free backward-difference estimate implies RH.

No Xi zero or divisor datum occurs in the hypotheses below.
-/

open Complex Filter Function Set

noncomputable section

namespace RHTower

/-- The exact completed-error difference, including the decaying endpoint value, is a direct
replacement for the dyadic weighted-prime inequality in the RH criterion. -/
theorem riemannHypothesis_of_eventually_completedErrorDifference_upper
    {N : ℕ} (hN : 2 ≤ N)
    (hdifference : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        criticalMellinCompletedError (Real.log n - Real.log 2) -
            criticalMellinCompletedError (Real.log n) +
            2 * (Real.sqrt 2 - 1) / Real.sqrt n ≤
          C * (n : ℝ) ^ epsilon) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
  intro epsilon hepsilon
  obtain ⟨C, hC, htail⟩ := hdifference epsilon hepsilon
  refine ⟨C, hC, fun n hn => ?_⟩
  rw [dyadicWeightedPrimeWindow_eq_floorSum]
  exact (dyadicWeightedPrimeWindow_upper_iff_completedErrorDifference
    (hN.trans hn) C epsilon).mpr (htail n hn)

/-- **Endpoint-free completed-error gate.**  RH follows if every positive power dominates the
backward `log 2` increment of the completed critical-Mellin error.  Thus the remaining arithmetic
burden is a one-sided subpower bound on two values of one source-defined scalar function. -/
theorem riemannHypothesis_of_eventually_completedError_backwardDifference_upper
    {N : ℕ} (hN : 2 ≤ N)
    (hdifference : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        criticalMellinCompletedError (Real.log n - Real.log 2) -
            criticalMellinCompletedError (Real.log n) ≤
          C * (n : ℝ) ^ epsilon) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_completedErrorDifference_upper hN
  intro epsilon hepsilon
  obtain ⟨C, hC, htail⟩ := hdifference epsilon hepsilon
  let D : ℝ := 2 * (Real.sqrt 2 - 1)
  have hsqrtTwo : 1 ≤ Real.sqrt 2 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨C + D, add_nonneg hC hD, fun n hn => ?_⟩
  have hnOneReal : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hsqrtOne : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnOneReal
  have hinv : (Real.sqrt n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrtOne
  have hpow : 1 ≤ (n : ℝ) ^ epsilon :=
    Real.one_le_rpow hnOneReal hepsilon.le
  have hfactor : 1 / Real.sqrt n ≤ (n : ℝ) ^ epsilon := by
    simpa only [one_div] using hinv.trans hpow
  have hendpoint :
      2 * (Real.sqrt 2 - 1) / Real.sqrt n ≤
        D * (n : ℝ) ^ epsilon := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using hfactor) hD
  have hmain := htail n hn
  dsimp only [D] at hendpoint ⊢
  nlinarith

end RHTower
