import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromLadder
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedAnnulusBound

/-!
# The Gallagher budget with the head paid by the ladder

The mean value theorem is sharp at the diagonal, so paying the frequencies below the Gallagher cut
with it returns exactly the trivial mean square.  The genuine estimate for that range is the ladder
bound, and only the frequencies above the cut may be paid by the mean value theorem — where the
kernel's quadratic decay makes the trivial bound harmless.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The prime polynomial of a block is at most the number of primes of the block. -/
theorem norm_primeBlockPoly_le_card (B : Finset ℕ) (w : ℝ) :
    ‖primeBlockPoly B w‖ ≤ (B.card : ℝ) := by
  classical
  rw [primeBlockPoly]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun p _ => norm_moebiusPhase_le_one w p).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The Gallagher-weighted spectral integral, with the head paid by the ladder bound.** -/
theorem integral_kernel_normSq_omegaWeighted_head_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {δ G β₀ : ℝ} (hδ : 0 < δ) (hG : 1 ≤ G)
    (hbound : (∫ w in Set.Icc (-G) G,
        ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤ β₀) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ 2
        * ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * δ ^ 2 * β₀
        + (4 * (5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖omegaCoeff P n‖ ^ 2)
              / (Real.pi ^ 2 * G)
            + 4 * (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖omegaCoeff P n‖ ^ 2)
              / (3 * Real.pi ^ 2 * G ^ 2)) := by
  classical
  set S : Finset ℕ := Finset.Icc A₀ B₀ with hS
  have hs0 : (0 : ℕ) ∉ S := by
    rw [hS, Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ S, n ≤ B₀ := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    exact hn.2
  have hbound' : (∫ w in Set.Icc (-G) G, ‖logPoly (omegaCoeff P) S w‖ ^ 2) ≤ β₀ := by
    refine le_trans (le_of_eq ?_) hbound
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [logPoly_omegaCoeff_eq]
  have hmaj := affineMajorant_of_bound_at (a := omegaCoeff P) hs0 hsM (W := G) (T₀ := G) hG
    hbound'
  have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG
  have hgal := gallagher_split_integral_dyadic_head (omegaCoeff P) S hδ hG0 hbound' hmaj
  rw [integral_normSq_logWindowSum_eq _ _ hδ.le] at hgal
  refine le_trans (le_of_eq ?_) hgal
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [logPoly_omegaCoeff_eq]

end

end RHTower.Sieve
