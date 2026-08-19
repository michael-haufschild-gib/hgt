import GaloisForLFunctions.RHTower.Sieve.Section4Assembly
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromLadder

/-!
# The Gallagher-weighted spectral integral for the joint weight

The mirror of `Sieve/OmegaBudgetFromLadder` for the `ω_P·ω_Q`-weighted polynomial: a bound on the
mean square at a single height `T₀`, together with the mean value theorem above that height, gives
an affine majorant, and Gallagher's dyadic split turns that into the kernel-weighted integral which
`jointOmegaBudget` holds.

Both ingredients (`Sieve/AffineMajorantFromHeight.affineMajorant_of_bound_at` and
`Sieve/GallagherDyadicTail.gallagher_split_integral_dyadic`) are stated for an arbitrary coefficient
sequence, so only the identification of the joint polynomial with a Gallagher polynomial and the
energy bound have to be supplied.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The joint coefficients, as a complex sequence. -/
def jointOmegaCoeff (P Q : Finset ℕ) (n : ℕ) : ℂ := ((jointOmegaWeight P Q n : ℝ) : ℂ)

theorem logPoly_jointOmegaCoeff_eq (P Q S : Finset ℕ) (w : ℝ) :
    logPoly (jointOmegaCoeff P Q) S w = jointOmegaPoly P Q S w :=
  logPoly_jointOmegaWeight_eq P Q S w

/-- The coefficient energy of the joint polynomial. -/
theorem energy_jointOmegaCoeff_le (P Q S : Finset ℕ) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hbd : ∀ n ∈ S, ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) ≤ Ω) :
    ∑ n ∈ S, ‖jointOmegaCoeff P Q n‖ ^ 2 ≤ (S.card : ℝ) * Ω ^ 2 := by
  classical
  have hterm : ∀ n ∈ S, ‖jointOmegaCoeff P Q n‖ ^ 2 ≤ Ω ^ 2 := by
    intro n hn
    have hnorm : ‖jointOmegaCoeff P Q n‖ = |jointOmegaWeight P Q n| := by
      rw [jointOmegaCoeff, Complex.norm_real, Real.norm_eq_abs]
    have hP0 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ ((primeFactorsIn Q n).card : ℝ) := Nat.cast_nonneg _
    have h1 := abs_moebius_real_le_one n
    have h4 : (0 : ℝ) ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)| := abs_nonneg _
    have h2 := hbd n hn
    rw [hnorm, jointOmegaWeight, abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hQ0]
    have hprod0 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) :=
      mul_nonneg hP0 hQ0
    have hA1 : |((ArithmeticFunction.moebius n : ℤ) : ℝ)|
        * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)) ≤ Ω := by
      nlinarith [h1, h2, hprod0, h4]
    have hA0 : (0 : ℝ) ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)|
        * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)) :=
      mul_nonneg h4 hprod0
    nlinarith [hA1, hA0]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The Gallagher-weighted spectral integral of the joint polynomial, from a bound at one
height.** -/
theorem integral_kernel_normSq_jointOmega_le {P Q : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {δ W T₀ β₀ : ℝ} (hδ : 0 < δ) (hW : 1 ≤ W)
    (hbound : (∫ w in Set.Icc (-T₀) T₀,
        ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ 2) ≤ β₀) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ 2
        * ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * δ ^ 2
          * ((5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ 2) * W
            + (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ 2))
        + (4 * (5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ 2)
              / (Real.pi ^ 2 * W)
            + 4 * (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ 2) / (3 * Real.pi ^ 2 * W ^ 2))
      := by
  classical
  set S : Finset ℕ := Finset.Icc A₀ B₀ with hS
  have hs0 : (0 : ℕ) ∉ S := by
    rw [hS, Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ S, n ≤ B₀ := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    exact hn.2
  have hbound' : (∫ w in Set.Icc (-T₀) T₀, ‖logPoly (jointOmegaCoeff P Q) S w‖ ^ 2) ≤ β₀ := by
    refine le_trans (le_of_eq ?_) hbound
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [logPoly_jointOmegaCoeff_eq]
  have hmaj := affineMajorant_of_bound_at (a := jointOmegaCoeff P Q) hs0 hsM (W := W) (T₀ := T₀)
    hW hbound'
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hgal := gallagher_split_integral_dyadic (jointOmegaCoeff P Q) S hδ hW0 hmaj
  rw [integral_normSq_logWindowSum_eq _ _ hδ.le] at hgal
  refine le_trans (le_of_eq ?_) hgal
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [logPoly_jointOmegaCoeff_eq]

end

end RHTower.Sieve
