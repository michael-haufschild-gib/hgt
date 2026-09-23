import GaloisForLFunctions.RHTower.Sieve.AffineMajorantFromHeight
import GaloisForLFunctions.RHTower.Sieve.OmegaSpectralFibre
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail

/-!
# From a ladder bound at one height to the Gallagher budget

The ladder estimate controls the mean square of the weighted polynomial up to a height `T₀` fixed by
the analytic input.  Gallagher's dyadic split needs a majorant at every height.  The mean value
theorem supplies the tail, and the two together give the weighted spectral integral that the Route E
gate consumes.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The coefficients of the weighted Möbius polynomial. -/
def omegaCoeff (P : Finset ℕ) (n : ℕ) : ℂ :=
  ((((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((primeFactorsIn P n).card : ℝ) : ℝ) : ℂ)

theorem logPoly_omegaCoeff_eq (P S : Finset ℕ) (w : ℝ) :
    logPoly (omegaCoeff P) S w = omegaWeightedMoebiusPoly P S w :=
  logPoly_omegaWeighted_eq P S w

/-- The coefficient energy of the weighted polynomial is at most the number of indices times the
square of the largest designated prime count. -/
theorem energy_omegaCoeff_le (P S : Finset ℕ) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hbd : ∀ n ∈ S, ((primeFactorsIn P n).card : ℝ) ≤ Ω) :
    ∑ n ∈ S, ‖omegaCoeff P n‖ ^ (2 : ℕ) ≤ (S.card : ℝ) * Ω ^ (2 : ℕ) := by
  classical
  have hterm : ∀ n ∈ S, ‖omegaCoeff P n‖ ^ (2 : ℕ) ≤ Ω ^ (2 : ℕ) := by
    intro n hn
    have hnorm : ‖omegaCoeff P n‖
        = |((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((primeFactorsIn P n).card : ℝ)| := by
      rw [omegaCoeff, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ))]
    have h1 := abs_moebius_real_le_one n
    have h2 := hbd n hn
    have h3 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)| := abs_nonneg _
    have hA1 : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * ((primeFactorsIn P n).card : ℝ) ≤ Ω := by
      nlinarith [h1, h2, h3, h4]
    have hA0 : (0 : ℝ)
        ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * ((primeFactorsIn P n).card : ℝ) :=
      mul_nonneg h4 h3
    nlinarith [hA1, hA0]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The Gallagher-weighted spectral integral, from a ladder bound at one height.** -/
theorem integral_kernel_normSq_omegaWeighted_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {δ W T₀ β₀ : ℝ} (hδ : 0 < δ) (hW : 1 ≤ W)
    (hbound : (∫ w in Set.Icc (-T₀) T₀,
        ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) ≤ β₀) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ (2 : ℕ)
        * ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ)
          * ((5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖omegaCoeff P n‖ ^ (2 : ℕ)) * W
            + (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖omegaCoeff P n‖ ^ (2 : ℕ)))
        + (4 * (5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖omegaCoeff P n‖ ^ (2 : ℕ))
              / (Real.pi ^ (2 : ℕ) * W)
            + 4 * (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖omegaCoeff P n‖ ^ (2 : ℕ)) / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ))) := by
  classical
  set S : Finset ℕ := Finset.Icc A₀ B₀ with hS
  have hs0 : (0 : ℕ) ∉ S := by
    rw [hS, Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ S, n ≤ B₀ := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    exact hn.2
  have hbound' : (∫ w in Set.Icc (-T₀) T₀, ‖logPoly (omegaCoeff P) S w‖ ^ (2 : ℕ)) ≤ β₀ := by
    refine le_trans (le_of_eq ?_) hbound
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [logPoly_omegaCoeff_eq]
  have hmaj := affineMajorant_of_bound_at (a := omegaCoeff P) hs0 hsM (W := W) (T₀ := T₀) hW
    hbound'
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hgal := gallagher_split_integral_dyadic (omegaCoeff P) S hδ hW0 hmaj
  rw [integral_normSq_logWindowSum_eq _ _ hδ.le] at hgal
  refine le_trans (le_of_eq ?_) hgal
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [logPoly_omegaCoeff_eq]

end

end RHTower.Sieve
