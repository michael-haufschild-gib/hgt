import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromAnnulus
import GaloisForLFunctions.RHTower.Sieve.SpectralHeadBound

/-!
# The Route E budget from a bound below the Gallagher cut

The spectral term of the budget is the Gallagher-weighted integral, which the dyadic split pays by
the head bound below the cut and the mean value theorem above it.  Everything else in the budget is
already explicit.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The Route E budget from a bound on the frequencies below the Gallagher cut.** -/
theorem omegaBudget_le_of_head {x h : ℝ} {z₀ z : ℕ} {G β₀ : ℝ}
    (hδ : 0 < fibreWidth x h) (hG : 1 ≤ G)
    (hhead : (∫ w in Set.Icc (-G) G,
        ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (fibreIndex x h) w‖ ^ (2 : ℕ)) ≤ β₀) :
    omegaBudget x h z₀ z
      ≤ 16 * Real.sqrt x
          * (2 * (fibreWidth x h) ^ (2 : ℕ) * β₀
            + (4 * (5 * Real.pi / 2
                  * ∑ n ∈ fibreIndex x h, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                / (Real.pi ^ (2 : ℕ) * G)
              + 4 * (β₀ + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
                    * ∑ n ∈ fibreIndex x h, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
        + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ (2 : ℕ) * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
              + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)) := by
  classical
  have hidx : fibreIndex x h = Finset.Icc 1 ⌊Real.sqrt x + h⌋₊ := rfl
  have hhead' : (∫ w in Set.Icc (-G) G,
      ‖omegaWeightedMoebiusPoly (primesRange z₀ z)
        (Finset.Icc 1 ⌊Real.sqrt x + h⌋₊) w‖ ^ (2 : ℕ)) ≤ β₀ := by
    rw [← hidx]
    exact hhead
  have hspec := integral_kernel_normSq_omegaWeighted_head_le
    (P := primesRange z₀ z) (A₀ := 1) (B₀ := ⌊Real.sqrt x + h⌋₊) (β₀ := β₀)
    (by omega) hδ hG hhead'
  rw [omegaBudget]
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hspec (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt x)
  rw [← hidx] at hmul
  linarith [hmul]

end

end RHTower.Sieve
