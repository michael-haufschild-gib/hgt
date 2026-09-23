import GaloisForLFunctions.RHTower.Sieve.Section4Assembly
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromLadder
import GaloisForLFunctions.RHTower.Sieve.JointBudgetTermSplit

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
    ∑ n ∈ S, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ) ≤ (S.card : ℝ) * Ω ^ (2 : ℕ) := by
  classical
  have hterm : ∀ n ∈ S, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ) ≤ Ω ^ (2 : ℕ) := by
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
        ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) ≤ β₀) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ (2 : ℕ)
        * ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ)
          * ((5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)) * W
            + (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)))
        + (4 * (5 * Real.pi / 2 * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ))
              / (Real.pi ^ (2 : ℕ) * W)
            + 4 * (β₀ + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)) / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ)))
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
  have hbound' : (∫ w in Set.Icc (-T₀) T₀, ‖logPoly (jointOmegaCoeff P Q) S w‖ ^ (2 : ℕ)) ≤ β₀ := by
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

/-- **The coefficient energy of the joint polynomial, at its true size.**  The crude bound
`energy_jointOmegaCoeff_le` pays `Ω = #P·#Q`; what the budget needs is `(length)·(W_P W_Q)²`, which
the joint Turán–Kubilius variance supplies. -/
theorem energy_jointOmegaCoeff_le_variance {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ))
      ≤ 2 * ((M : ℝ) * (Joint.mass P * Joint.mass Q)
              * (Joint.mass P + Joint.mass Q + 1)
            + 2 * (Joint.mass P * Joint.mass Q) * (P.card : ℝ) * (Q.card : ℝ))
        + 2 * (M : ℝ) * (Joint.mass P * Joint.mass Q) ^ (2 : ℕ) := by
  classical
  have hvar := sum_sq_joint_deviation_le hP hQ hPQ M
  simp only [Joint.mass]
  set WP : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ) with hWP
  set WQ : ℝ := ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) with hWQ
  have hterm : ∀ n ∈ Finset.Icc 1 M, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)
      ≤ 2 * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) - WP * WQ) ^ (2 : ℕ)
        + 2 * (WP * WQ) ^ (2 : ℕ) := by
    intro n _
    have hP0 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ ((primeFactorsIn Q n).card : ℝ) := Nat.cast_nonneg _
    have hnorm : ‖jointOmegaCoeff P Q n‖
        ≤ ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) := by
      rw [jointOmegaCoeff, Complex.norm_real, Real.norm_eq_abs, jointOmegaWeight, abs_mul,
        abs_mul, abs_of_nonneg hP0, abs_of_nonneg hQ0]
      have h1 := abs_moebius_real_le_one n
      have hprod0 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) :=
        mul_nonneg hP0 hQ0
      nlinarith [h1, hprod0, abs_nonneg ((ArithmeticFunction.moebius n : ℤ) : ℝ)]
    have h0 : (0 : ℝ) ≤ ‖jointOmegaCoeff P Q n‖ := norm_nonneg _
    have hsq : ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)
        ≤ (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hnorm, h0]
    nlinarith [hsq,
      sq_nonneg (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)
        - 2 * (WP * WQ))]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  have hcard : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by
    have hMM : M + 1 - 1 = M := by omega
    rw [hMM]
  rw [hcard]
  linarith [hvar]

/-- **The Gallagher-weighted spectral integral of the joint polynomial, in its final form.**  The
expiry height `T₀` is free — it only has to be positive — and the two surviving terms are the
majorant's slope over the cut and its constant over the cut squared. -/
theorem integral_kernel_normSq_jointOmega_le' {P Q : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {δ Wc T₀ β₀ : ℝ} (hδ : 0 < δ) (hWc : 1 ≤ Wc) (hT₀ : 0 < T₀) (hδWc : δ * Wc ≤ 1)
    (hbound : (∫ w in Set.Icc (-T₀) T₀,
        ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) ≤ β₀) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ (2 : ℕ)
        * ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ 3 * ((5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((B₀ : ℝ) / T₀))
            * ∑ n ∈ Finset.Icc A₀ B₀, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)) / Wc
        + 3 * β₀ / Wc ^ (2 : ℕ) := by
  classical
  set S : Finset ℕ := Finset.Icc A₀ B₀ with hS
  have hs0 : (0 : ℕ) ∉ S := by
    rw [hS, Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ S, n ≤ B₀ := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    exact hn.2
  have hbound' : (∫ w in Set.Icc (-T₀) T₀, ‖logPoly (jointOmegaCoeff P Q) S w‖ ^ (2 : ℕ)) ≤ β₀ := by
    refine le_trans (le_of_eq ?_) hbound
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [logPoly_jointOmegaCoeff_eq]
  have hβ0 : (0 : ℝ) ≤ β₀ := by
    refine le_trans ?_ hbound'
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => ?_
    positivity
  have hmaj := affineMajorant_of_bound_at' (a := jointOmegaCoeff P Q) hs0 hsM (Wc := Wc)
    (T₀ := T₀) (β₀ := β₀) hWc hT₀ hbound'
  have hWc0 : (0 : ℝ) < Wc := lt_of_lt_of_le zero_lt_one hWc
  have hgal := gallagher_split_integral_dyadic (jointOmegaCoeff P Q) S hδ hWc0 hmaj
  rw [integral_normSq_logWindowSum_eq _ _ hδ.le] at hgal
  set α : ℝ := (5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((B₀ : ℝ) / T₀))
      * ∑ n ∈ S, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ) with hαdef
  have hα0 : (0 : ℝ) ≤ α := by
    rw [hαdef]
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((B₀ : ℝ) / T₀) := by
      have h2 : (0 : ℝ) ≤ (B₀ : ℝ) / T₀ := div_nonneg (Nat.cast_nonneg _) hT₀.le
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith
    exact mul_nonneg h1 (Finset.sum_nonneg fun n _ => by positivity)
  have harith := joint_spectral_terms_le (Wc := Wc) (α := α) (β₀ := β₀) (δ := δ) hWc0 hδ.le
    hδWc hα0 hβ0
  have hrw : (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ (2 : ℕ)
      * ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      = ∫ w : ℝ, ‖logWindowKernel δ w‖ ^ (2 : ℕ) * ‖logPoly (jointOmegaCoeff P Q) S w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [logPoly_jointOmegaCoeff_eq, hS]
  rw [hrw]
  linarith [hgal, harith]

end

end RHTower.Sieve
