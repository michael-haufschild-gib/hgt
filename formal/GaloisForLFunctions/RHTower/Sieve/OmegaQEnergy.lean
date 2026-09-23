import GaloisForLFunctions.RHTower.Sieve.JointLadderProduct
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedLadderBound

/-!
# The coefficient energy of the long-weighted cofactor

The non-exceptional half of exposé §4 applies the mean value theorem to the cofactor polynomial
`∑_m μ(m)ω_Q(m)m^{iw}`.  Bounding its coefficients by `#Q` — the crude bound of
`Sieve/JointLadderProduct.norm_omegaQCoeff_le` — is far too lossy there: what the estimate needs is
the *energy* `∑_m ω_Q(m)²`, which Turán–Kubilius pins to `≍ (length)·W(Q)²`.

The two are wildly different: `#Q` is of the size of the long primes themselves, while `W(Q)` is
`≍ log log`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The energy of the long-weighted cofactor over an interval.** -/
theorem sum_normSq_omegaQCoeff_Ioc_le {q₀ q₁ : ℕ} (hq : q₀ ≤ q₁) (a b : ℕ) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b, ‖omegaQCoeff (primesRange q₀ q₁) n‖ ^ (2 : ℕ))
      ≤ 2 * (4 * ((b : ℝ) - a) * mertensS q₁ + 4 * ((Nat.primesLE q₁).card : ℝ)
            + 8 * ((Nat.primesLE q₁).card : ℝ) ^ (2 : ℕ))
        + 2 * ((b : ℝ) - a) * (mertensS q₁ - mertensS q₀) ^ (2 : ℕ) := by
  classical
  set Q : Finset ℕ := primesRange q₀ q₁ with hQ
  set WQ : ℝ := mertensS q₁ - mertensS q₀ with hWQ
  have hterm : ∀ n ∈ Finset.Ioc a b, ‖omegaQCoeff Q n‖ ^ (2 : ℕ)
      ≤ 2 * (((primeFactorsIn Q n).card : ℝ) - WQ) ^ (2 : ℕ) + 2 * WQ ^ (2 : ℕ) := by
    intro n _
    have hnorm : ‖omegaQCoeff Q n‖
        ≤ ((primeFactorsIn Q n).card : ℝ) := by
      rw [omegaQCoeff, norm_mul, Complex.norm_natCast]
      have h1 := norm_moebiusCoeff_le_one n
      have h2 : (0 : ℝ) ≤ ((primeFactorsIn Q n).card : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, h2, norm_nonneg (moebiusCoeff n)]
    have h0 : (0 : ℝ) ≤ ‖omegaQCoeff Q n‖ := norm_nonneg _
    have hsq : ‖omegaQCoeff Q n‖ ^ (2 : ℕ) ≤ ((primeFactorsIn Q n).card : ℝ) ^ (2 : ℕ) := by
      nlinarith [hnorm, h0]
    nlinarith [hsq, sq_nonneg (((primeFactorsIn Q n).card : ℝ) - 2 * WQ)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
  have hvar := sum_variance_primesRange_le hq a b hab
  have hcard : ((b - a : ℕ) : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub hab]
  have hW2 : (0 : ℝ) ≤ WQ ^ (2 : ℕ) := sq_nonneg _
  nlinarith [hvar, hcard, hW2]

/-- **The mean value theorem for the long-weighted cofactor, at its true energy.** -/
theorem integral_Icc_normSq_omegaWeighted_le_energy {q₀ q₁ : ℕ} {a b : ℕ}
    (ha : 1 ≤ a) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W,
        ‖omegaWeightedMoebiusPoly (primesRange q₀ q₁) (Finset.Icc a b) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (b : ℝ))
        * (∑ n ∈ Finset.Ioc (a - 1) b, ‖omegaQCoeff (primesRange q₀ q₁) n‖ ^ (2 : ℕ)) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ Finset.Icc a b, n ≤ b := fun n hn => (Finset.mem_Icc.1 hn).2
  have hbase := integral_Icc_normSq_logPoly_le_energy (omegaQCoeff (primesRange q₀ q₁))
    hs0 hsM hW
  have hrw : (∫ w in Set.Icc (-W) W,
      ‖omegaWeightedMoebiusPoly (primesRange q₀ q₁) (Finset.Icc a b) w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-W) W, ‖logPoly (omegaQCoeff (primesRange q₀ q₁)) (Finset.Icc a b) w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [omegaWeightedMoebiusPoly_eq_logPoly]
  rw [hrw]
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => by positivity
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc]
    omega
  · have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
    nlinarith [hW, hpi, he, hb]

/-- **Lemma 2.4 for the long-weighted cofactor over a part of the window.** -/
theorem setIntegral_normSq_omegaWeighted_le_energy_on {q₀ q₁ : ℕ} {a b : ℕ}
    (ha : 1 ≤ a) {W : ℝ} (hW : 1 ≤ W) {S : Set ℝ} (hSs : S ⊆ Set.Icc (-W) W) :
    (∫ w in S, ‖omegaWeightedMoebiusPoly (primesRange q₀ q₁) (Finset.Icc a b) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (b : ℝ))
        * (∑ n ∈ Finset.Ioc (a - 1) b, ‖omegaQCoeff (primesRange q₀ q₁) n‖ ^ (2 : ℕ)) := by
  classical
  have hcont : Continuous fun w : ℝ =>
      ‖omegaWeightedMoebiusPoly (primesRange q₀ q₁) (Finset.Icc a b) w‖ ^ (2 : ℕ) :=
    (((continuous_omegaWeightedMoebiusPoly _ _).norm).pow 2)
  have hmono : (∫ w in S, ‖omegaWeightedMoebiusPoly (primesRange q₀ q₁) (Finset.Icc a b) w‖ ^ (2 : ℕ))
      ≤ ∫ w in Set.Icc (-W) W,
          ‖omegaWeightedMoebiusPoly (primesRange q₀ q₁) (Finset.Icc a b) w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc ?_
      (Filter.Eventually.of_forall hSs)
    exact Filter.Eventually.of_forall fun w => by positivity
  exact hmono.trans (integral_Icc_normSq_omegaWeighted_le_energy ha hW)

end

end RHTower.Sieve
