import GaloisForLFunctions.ArithmeticCountingPositivity.TheDivisorCountHasAPositiveRenewalKernel
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughMeanAtAFixedScale

/-!
# The positive divisor mean controls the signed primitive

Harmonic divisor swapping writes the positive mean as the signed gauge averaged against
harmonic numbers. Their bounded logarithmic remainder gives an error of order `log N`
between that mean and the signed polar moment, without any density hypothesis.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- Harmonic divisor swapping identifies the positive mean with a harmonic smoothing
of the original signs. -/
theorem gaugeHarmonicSum_signDivisorCount_eq (ω : ℕ → ℝ) (N : ℕ) :
    gaugeHarmonicSum (signDivisorCount ω) N =
      ∑ d ∈ Icc 1 N, ω d / d * gaugeHarmonicSum (fun _ => 1) (N / d) := by
  have hterm : ∀ n ∈ Icc 1 N, signDivisorCount ω n / n =
      ∑ d ∈ n.divisors, ω d / d * (1 / (n / d : ℕ)) := by
    intro n _
    rw [signDivisorCount, sum_div]
    refine sum_congr rfl fun d hd => ?_
    have hdn : (d : ℝ) * (n / d : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    rw [div_mul_div_comm, mul_one, hdn]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, ω d / d * (1 / (n / d : ℕ)) :=
      sum_congr rfl hterm
    _ = ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d), ω d / d * (1 / (k : ℝ)) :=
      RHTower.Sieve.sum_divisors_swap N (fun d k => ω d / d * (1 / (k : ℝ)))
    _ = _ := sum_congr rfl fun d _ => (mul_sum _ _ _).symm

private theorem abs_positiveMean_sub_logWeightSum_le (P : Set ℕ) (N : ℕ) :
    |gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N - logWeightSum (primeSetFlip P) N| ≤
      gaugeHarmonicSum (fun _ => 1) N := by
  rw [gaugeHarmonicSum_signDivisorCount_eq, logWeightSum_eq, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 N,
        |primeSetFlip P d / d * gaugeHarmonicSum (fun _ => 1) (N / d) -
          primeSetFlip P d / d * Real.log (N / d : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) / d := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      rw [← mul_sub, abs_mul, abs_div, abs_of_pos hd0]
      calc
        _ ≤ (1 / (d : ℝ)) * 1 := mul_le_mul
          (div_le_div_of_nonneg_right (abs_primeSetFlip_le P d) hd0.le)
          (abs_harmonic_sub_log_le (N / d)) (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    _ = _ := rfl

/-- The positive divisor mean and the signed polar moment differ by at most `3 + log N`,
with no assumption on the flipped primes. -/
theorem abs_positiveDivisorMean_sub_signedPolarMoment_le (P : Set ℕ) (N : ℕ) :
    |gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N - polarMoment (primeSetFlip P) N| ≤
      3 + Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [gaugeHarmonicSum, polarMoment]
  have hhead := abs_positiveMean_sub_logWeightSum_le P N
  have htail := abs_polarMoment_sub_logWeightSum_le (abs_primeSetFlip_le P) hN
  rw [abs_sub_comm] at htail
  have hH := (abs_le.mp (abs_harmonic_sub_log_le N)).2
  have htri := abs_sub_le
    (gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N)
    (logWeightSum (primeSetFlip P) N) (polarMoment (primeSetFlip P) N)
  linarith only [hhead, htail, hH, htri]

private theorem sum_hyperbolic_swap (a b : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ Icc 1 N, a d * ∑ k ∈ Icc 1 (N / d), b k =
      ∑ d ∈ Icc 1 N, b d * ∑ k ∈ Icc 1 (N / d), a k := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d) := by
      simpa only [mul_sum] using (RHTower.Sieve.sum_divisors_swap N (fun d k => a d * b k)).symm
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, b d * a (n / d) := by
      refine sum_congr rfl fun n _ => ?_
      rw [← Nat.sum_divisorsAntidiagonal (fun d k => a d * b k),
        Nat.sum_divisorsAntidiagonal' (fun d k => a d * b k)]
      exact sum_congr rfl fun d _ => mul_comm _ _
    _ = _ := by
      simpa only [mul_sum] using RHTower.Sieve.sum_divisors_swap N (fun d k => b d * a k)

private def fullPrimeRenewalTerm (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 N with p.Prime, Real.log p / p * gaugeHarmonicSum ω (N / p)

private def higherPrimePowerRenewalTerm (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N with ¬ d.Prime, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)

/-- The contribution of the flipped primes to the signed renewal equation. -/
def flippedPrimeRenewalTerm (P : Set ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ primeSetCutoff P N, Real.log p / p * gaugeHarmonicSum (primeSetFlip P) (N / p)

private theorem fullPrimeRenewalTerm_eq (ω : ℕ → ℝ) (N : ℕ) :
    fullPrimeRenewalTerm ω N =
      ∑ m ∈ Icc 1 N, ω m / m * primeMean (fun _ => 1) (N / m) := by
  have h := sum_hyperbolic_swap (fun p => if p.Prime then Real.log p / p else 0)
    (fun m => ω m / m) N
  simpa only [fullPrimeRenewalTerm, gaugeHarmonicSum, primeMean, sum_filter,
    one_mul, ite_mul, zero_mul] using h

private theorem abs_fullPrimeRenewalTerm_sub_logWeightSum_le (P : Set ℕ) (N : ℕ) :
    |fullPrimeRenewalTerm (primeSetFlip P) N - logWeightSum (primeSetFlip P) N| ≤
      ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) * gaugeHarmonicSum (fun _ => 1) N := by
  let C₁ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  rw [fullPrimeRenewalTerm_eq, logWeightSum_eq, ← sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ Icc 1 N,
        |primeSetFlip P m / m * primeMean (fun _ => 1) (N / m) -
          primeSetFlip P m / m * Real.log (N / m : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Icc 1 N, C₁ * (1 / (m : ℝ)) := by
      apply sum_le_sum
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le (mem_Icc.mp hm).1).mpr
        (by simpa using (mem_Icc.mp hm).2)
      have hA : |primeMean (fun _ => 1) (N / m) - Real.log (N / m : ℕ)| ≤ C₁ := by
        simpa only [primeMean, one_mul] using RHTower.Mertens.mertens_first_prime (N / m) hq
      rw [← mul_sub, abs_mul, abs_div, abs_of_pos hm0]
      exact (mul_le_mul (div_le_div_of_nonneg_right (abs_primeSetFlip_le P m) hm0.le)
        hA (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
    _ = _ := by rw [← mul_sum]; rfl

private theorem prime_flip_renewal_split (P : Set ℕ) (N : ℕ) :
    (∑ p ∈ Icc 1 N with p.Prime,
      primeSetFlip P p * Real.log p / p * gaugeHarmonicSum (primeSetFlip P) (N / p)) =
      fullPrimeRenewalTerm (primeSetFlip P) N - 2 * flippedPrimeRenewalTerm P N := by
  classical
  unfold fullPrimeRenewalTerm flippedPrimeRenewalTerm
  rw [primeSetCutoff_eq_filter, sum_filter (s := (Icc 1 N).filter Nat.Prime),
    mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hprime := (mem_filter.mp hp).2
  by_cases h : p ∈ P
  · rw [if_pos h, primeSetFlip_prime_of_mem P hprime h]
    ring
  · rw [if_neg h, primeSetFlip_prime_of_notMem P hprime h]
    ring

private theorem abs_higherPrimePowerRenewalTerm_le (P : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |higherPrimePowerRenewalTerm (primeSetFlip P) N| ≤
      (2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) * (1 + Real.log N) := by
  unfold higherPrimePowerRenewalTerm
  calc
    _ ≤ ∑ d ∈ Icc 1 N with ¬ d.Prime,
        |Λ d * (primeSetFlip P d / d) * gaugeHarmonicSum (primeSetFlip P) (N / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N with ¬ d.Prime, (Λ d / d) * (1 + Real.log N) := by
      apply sum_le_sum
      intro d hd
      have hdI := (mem_filter.mp hd).1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hdI).1
      have hq : 1 ≤ N / d := (Nat.le_div_iff_mul_le (mem_Icc.mp hdI).1).mpr
        (by simpa using (mem_Icc.mp hdI).2)
      have hq0 : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast hq
      have hqN : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
      have hS : |gaugeHarmonicSum (primeSetFlip P) (N / d)| ≤ 1 + Real.log N := by
        have habs := abs_gaugeHarmonicSum_le (primeSetFlip P) (abs_primeSetFlip_le P) (N / d)
        have hlog := Real.log_le_log hq0 hqN
        linarith only [habs, hlog]
      have hcoeff : |Λ d * (primeSetFlip P d / d)| ≤ Λ d / d := by
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_div, abs_of_pos hd0]
        have h := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (abs_primeSetFlip_le P d) hd0.le)
          (ArithmeticFunction.vonMangoldt_nonneg (n := d))
        exact h.trans_eq (by ring)
      rw [abs_mul]
      exact mul_le_mul hcoeff hS (abs_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_vonMangoldt_nonprime_le hN)
        (by linarith only [Real.log_natCast_nonneg N])

private theorem logMoment_primeSetFlip_renewal (P : Set ℕ) (N : ℕ) :
    logMoment (primeSetFlip P) N = fullPrimeRenewalTerm (primeSetFlip P) N -
      2 * flippedPrimeRenewalTerm P N + higherPrimePowerRenewalTerm (primeSetFlip P) N := by
  rw [logMoment_eq_vonMangoldt (primeSetFlip P)
    (fun _ _ ha hb => (primeSetFlip_isSignGauge P).mul ha hb)]
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
    (fun d => Λ d * (primeSetFlip P d / d) * gaugeHarmonicSum (primeSetFlip P) (N / d))
  have hprime : (∑ d ∈ Icc 1 N with d.Prime,
      Λ d * (primeSetFlip P d / d) * gaugeHarmonicSum (primeSetFlip P) (N / d)) =
      ∑ d ∈ Icc 1 N with d.Prime,
        primeSetFlip P d * Real.log d / d * gaugeHarmonicSum (primeSetFlip P) (N / d) := by
    refine sum_congr rfl fun d hd => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]
    ring
  rw [hprime, prime_flip_renewal_split] at hsplit
  exact hsplit.symm

/-- The signed renewal equation has a logarithmic remainder for every prime pattern. -/
theorem exists_abs_signed_flip_renewal_equation_le (P : Set ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |gaugeHarmonicSum (primeSetFlip P) N * Real.log N -
        2 * polarMoment (primeSetFlip P) N + 2 * flippedPrimeRenewalTerm P N| ≤
          K * (1 + Real.log N) := by
  let C₁ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  let C₂ := 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  refine ⟨|C₁| + |C₂| + 2, by positivity, fun N hN => ?_⟩
  have hlog := Real.log_natCast_nonneg N
  have hH0 : 0 ≤ gaugeHarmonicSum (fun _ => (1 : ℝ)) N := by
    unfold gaugeHarmonicSum
    exact sum_nonneg fun n _ => by positivity
  have hH := (abs_le.mp (abs_harmonic_sub_log_le N)).2
  have hhead := abs_fullPrimeRenewalTerm_sub_logWeightSum_le P N
  have hmoment := abs_polarMoment_sub_logWeightSum_le (abs_primeSetFlip_le P) hN
  rw [abs_sub_comm] at hmoment
  have htail := abs_higherPrimePowerRenewalTerm_le P hN
  have htri₁ := abs_sub_le (fullPrimeRenewalTerm (primeSetFlip P) N)
    (logWeightSum (primeSetFlip P) N) (polarMoment (primeSetFlip P) N)
  have htri₂ := abs_add_le
    (fullPrimeRenewalTerm (primeSetFlip P) N - polarMoment (primeSetFlip P) N)
    (higherPrimePowerRenewalTerm (primeSetFlip P) N)
  have hC₁H : C₁ * gaugeHarmonicSum (fun _ => (1 : ℝ)) N ≤ |C₁| * (1 + Real.log N) := by
    exact (mul_le_mul_of_nonneg_right (le_abs_self C₁) hH0).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hH]) (abs_nonneg C₁))
  have hC₂H := mul_le_mul_of_nonneg_right (le_abs_self C₂)
    (show 0 ≤ 1 + Real.log N by linarith only [hlog])
  have heq : gaugeHarmonicSum (primeSetFlip P) N * Real.log N -
      2 * polarMoment (primeSetFlip P) N + 2 * flippedPrimeRenewalTerm P N =
      (fullPrimeRenewalTerm (primeSetFlip P) N - polarMoment (primeSetFlip P) N) +
        higherPrimePowerRenewalTerm (primeSetFlip P) N := by
    have h := logMoment_primeSetFlip_renewal P N
    rw [logMoment_eq] at h
    linarith only [h]
  rw [heq]
  change _ ≤ (|C₁| + |C₂| + 2) * (1 + Real.log N)
  change |fullPrimeRenewalTerm (primeSetFlip P) N - logWeightSum (primeSetFlip P) N| ≤
    C₁ * gaugeHarmonicSum (fun _ => 1) N at hhead
  change |higherPrimePowerRenewalTerm (primeSetFlip P) N| ≤ C₂ * (1 + Real.log N) at htail
  nlinarith only [hhead, hmoment, htail, htri₁, htri₂, hC₁H, hC₂H, hlog]

/-- The uniform lower bound on signed harmonic sums controls the negative renewal part. -/
theorem neg_primeSetLogMass_le_flippedPrimeRenewalTerm (P : Set ℕ) (N : ℕ) :
    -primeSetLogMass P N ≤ flippedPrimeRenewalTerm P N := by
  rw [primeSetLogMass, flippedPrimeRenewalTerm, ← sum_neg_distrib]
  apply sum_le_sum
  intro p _
  have h := mul_le_mul_of_nonneg_left
    (neg_one_le_gaugeHarmonicSum (primeSetFlip_isSignGauge P) (N / p))
    (show 0 ≤ Real.log p / p from div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))
  simpa only [mul_neg_one] using h

end GaloisForLFunctions.RenormalizedIntersectionTheory

