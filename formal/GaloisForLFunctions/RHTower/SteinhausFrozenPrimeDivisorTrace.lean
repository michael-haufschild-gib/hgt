import GaloisForLFunctions.RHTower.SteinhausLargestPrimeDecomposition
import GaloisForLFunctions.RHTower.SteinhausPhaseRotation
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries

/-!
# Divisor traces with frozen large-prime phases

Below the square of the phase cutoff, the exact largest-prime split has
only a smooth background and linear negative prime channels.
-/

set_option autoImplicit false
open MeasureTheory Complex Finset Nat
noncomputable section
namespace RHTower
open SteinhausModel
open GaloisForLFunctions.RHTower

/-- Large prime phases are fixed at minus one; small phases remain free. -/
def frozenPrimePhase (Y : ℕ) (ω : Omega) : Omega :=
  fun p => if p ≤ Y then ω p else 1 / 2

/-- The Steinhaus character as an arithmetic function, with its required zero value. -/
def steinhausArithmetic (ω : Omega) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else X n ω
  map_zero' := by simp

/-- The conjugate arithmetic character. -/
def steinhausConjugateArithmetic (ω : Omega) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else (starRingEnd ℂ) (X n ω)
  map_zero' := by simp

private theorem steinhausArithmetic_apply {n : ℕ} (hn : n ≠ 0) (ω : Omega) :
    steinhausArithmetic ω n = X n ω := by
  simp [steinhausArithmetic, hn]

private theorem steinhausConjugateArithmetic_apply {n : ℕ} (hn : n ≠ 0) (ω : Omega) :
    steinhausConjugateArithmetic ω n = (starRingEnd ℂ) (X n ω) := by
  simp [steinhausConjugateArithmetic, hn]

/-- The product-fibre trace of an arithmetic phase. -/
def steinhausDivisorTrace (ω : Omega) : ArithmeticFunction ℂ :=
  steinhausArithmetic ω * steinhausConjugateArithmetic ω

private theorem steinhausArithmetic_isMultiplicative (ω : Omega) :
    (steinhausArithmetic ω).IsMultiplicative := by
  refine ⟨by simp [steinhausArithmetic, X_one], ?_⟩
  intro m n _
  by_cases hm : m = 0
  · simp [hm, steinhausArithmetic]
  by_cases hn : n = 0
  · simp [hn, steinhausArithmetic]
  simp only [steinhausArithmetic_apply (Nat.mul_ne_zero hm hn),
    steinhausArithmetic_apply hm, steinhausArithmetic_apply hn, X_mul hm hn]

private theorem steinhausConjugateArithmetic_isMultiplicative (ω : Omega) :
    (steinhausConjugateArithmetic ω).IsMultiplicative := by
  refine ⟨by simp [steinhausConjugateArithmetic, X_one], ?_⟩
  intro m n _
  by_cases hm : m = 0
  · simp [hm, steinhausConjugateArithmetic]
  by_cases hn : n = 0
  · simp [hn, steinhausConjugateArithmetic]
  simp only [steinhausConjugateArithmetic_apply (Nat.mul_ne_zero hm hn),
    steinhausConjugateArithmetic_apply hm, steinhausConjugateArithmetic_apply hn,
    X_mul hm hn, map_mul]

/-- Coprime product fibres factor even though the divisor trace is not completely multiplicative. -/
theorem steinhausDivisorTrace_isMultiplicative (ω : Omega) :
    (steinhausDivisorTrace ω).IsMultiplicative :=
  (steinhausArithmetic_isMultiplicative ω).mul
    (steinhausConjugateArithmetic_isMultiplicative ω)

/-- The convolution contains exactly the ordered divisors of the product. -/
theorem steinhausDivisorTrace_eq_sum (n : ℕ) (ω : Omega) :
    steinhausDivisorTrace ω n = ∑ d ∈ n.divisorsAntidiagonal,
      X d.1 ω * (starRingEnd ℂ) (X d.2 ω) := by
  rw [steinhausDivisorTrace, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [steinhausArithmetic_apply (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd),
    steinhausConjugateArithmetic_apply (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd)]

private theorem measurable_frozenPrimePhase (Y : ℕ) : Measurable (frozenPrimePhase Y) := by
  apply measurable_pi_lambda
  intro p
  by_cases hp : p ≤ Y
  · simpa only [frozenPrimePhase, if_pos hp] using measurable_pi_apply p
  · simpa only [frozenPrimePhase, if_neg hp] using
      (measurable_const : Measurable (fun _ : Omega => (1 / 2 : ℝ)))

/-- Every frozen pair character is integrable on the probability space. -/
theorem integrable_frozenPrime_pair (Y n m : ℕ) :
    Integrable (fun ω => X n (frozenPrimePhase Y ω) *
      (starRingEnd ℂ) (X m (frozenPrimePhase Y ω))) steinhausMeasure := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (((measurable_X n).comp (measurable_frozenPrimePhase Y)).mul
      (continuous_star.measurable.comp
        ((measurable_X m).comp (measurable_frozenPrimePhase Y)))).aestronglyMeasurable
  · filter_upwards with ω
    rw [norm_mul, norm_X, RCLike.norm_conj, norm_X, one_mul]

/-- The frozen product-fibre trace is absolutely integrable. -/
theorem integrable_frozenPrime_divisorTrace (Y n : ℕ) :
    Integrable (fun ω => steinhausDivisorTrace (frozenPrimePhase Y ω) n) steinhausMeasure := by
  simp_rw [steinhausDivisorTrace_eq_sum]
  exact integrable_finsetSum _ fun d _ => integrable_frozenPrime_pair Y d.1 d.2

/-- Only equal ordered divisors survive averaging all prime phases. -/
theorem integral_steinhausDivisorTrace (n : ℕ) :
    (∫ ω, steinhausDivisorTrace ω n ∂steinhausMeasure) =
      ∑ d ∈ n.divisorsAntidiagonal, if d.1 = d.2 then (1 : ℂ) else 0 := by
  simp_rw [steinhausDivisorTrace_eq_sum]
  rw [integral_finsetSum _ (fun d _ => integrable_X_mul_conj d.1 d.2)]
  apply Finset.sum_congr rfl
  intro d hd
  exact integral_X_mul_conj (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd)
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd)

/-- Freezing leaves every smooth character unchanged. -/
theorem X_frozenPrimePhase_eq {Y n : ℕ}
    (hn : ∀ p ∈ n.primeFactors, p ≤ Y) (ω : Omega) :
    X n (frozenPrimePhase Y ω) = X n ω := by
  apply X_congr_of_eqOn_primeFactors
  intro p hp
  exact if_pos (hn p hp)

/-- The complete divisor trace of a smooth product reads only unfrozen phases. -/
theorem steinhausDivisorTrace_frozen_eq {Y n : ℕ}
    (hn : ∀ p ∈ n.primeFactors, p ≤ Y) (ω : Omega) :
    steinhausDivisorTrace (frozenPrimePhase Y ω) n = steinhausDivisorTrace ω n := by
  rw [steinhausDivisorTrace_eq_sum, steinhausDivisorTrace_eq_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hd
  have h1 : ∀ p ∈ d.1.primeFactors, p ≤ Y := by
    intro p hp
    exact hn p (Nat.primeFactors_mono
      (hprod ▸ dvd_mul_right d.1 d.2) hn0 hp)
  have h2 : ∀ p ∈ d.2.primeFactors, p ≤ Y := by
    intro p hp
    exact hn p (Nat.primeFactors_mono
      (hprod ▸ dvd_mul_left d.2 d.1) hn0 hp)
  rw [X_frozenPrimePhase_eq h1, X_frozenPrimePhase_eq h2]

/-- The two ordered prime divisors both carry the frozen negative phase. -/
theorem steinhausDivisorTrace_frozen_prime {Y p : ℕ}
    (hp : p.Prime) (hpY : Y < p) (ω : Omega) :
    steinhausDivisorTrace (frozenPrimePhase Y ω) p = -2 := by
  have hx : X p (frozenPrimePhase Y ω) = -1 := by
    rw [X_prime_eq hp]
    simp only [frozenPrimePhase, if_neg (not_le.mpr hpY)]
    exact cexp_two_pi_I_div_two
  rw [steinhausDivisorTrace, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      steinhausArithmetic (frozenPrimePhase Y ω) a *
        steinhausConjugateArithmetic (frozenPrimePhase Y ω) b),
    hp.divisors, Finset.sum_insert (by rw [Finset.mem_singleton]; exact hp.one_lt.ne),
    Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos]
  norm_num [steinhausArithmetic, steinhausConjugateArithmetic, hp.ne_zero, X_one, hx]

/-- A product below the first large-prime seam retains exactly one negative prime factor. -/
theorem steinhausDivisorTrace_frozen_largePrime_mul {Y p m : ℕ}
    (hp : p.Prime) (hpY : Y < p) (hm0 : 0 < m) (hmY : m < Y) (ω : Omega) :
    steinhausDivisorTrace (frozenPrimePhase Y ω) (p * m) =
      -2 * steinhausDivisorTrace ω m := by
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    exact (not_le.mpr (hmY.trans hpY)) (Nat.le_of_dvd hm0 hdiv))
  rw [(steinhausDivisorTrace_isMultiplicative _).map_mul_of_coprime hcop,
    steinhausDivisorTrace_frozen_prime hp hpY]
  have hms : ∀ q ∈ m.primeFactors, q ≤ Y := by
    intro q hq
    exact (Nat.le_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hq)).trans hmY.le
  rw [steinhausDivisorTrace_frozen_eq hms]

/-- The deterministic diagonal left by independent phase averaging. -/
def divisorDiagonalMass (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisorsAntidiagonal, if d.1 = d.2 then 1 else 0

/-- Exactly one equal divisor pair exists for a positive square, and none otherwise. -/
theorem divisorDiagonalMass_eq_squareIndicator {n : ℕ} (hn : n ≠ 0) :
    divisorDiagonalMass n = squareIndicator n := by
  classical
  unfold divisorDiagonalMass squareIndicator
  by_cases hsq : IsSquare n
  · rw [if_pos hsq]
    obtain ⟨d, hd⟩ := hsq
    calc
      _ = (if d = d then (1 : ℂ) else 0) := by
        apply Finset.sum_eq_single (d, d)
        · intro x hx hxne
          by_cases he : x.1 = x.2
          · exfalso
            have hprod : x.1 * x.1 = d * d := by
              simpa only [← he] using (Nat.mem_divisorsAntidiagonal.mp hx).1.trans hd
            have hroot : x.1 = d := Nat.pow_left_injective (by norm_num)
              (show x.1 ^ 2 = d ^ 2 by simpa only [pow_two] using hprod)
            exact hxne (Prod.ext hroot (he.symm.trans hroot))
          · exact if_neg he
        · intro hnot
          exact False.elim (hnot (Nat.mem_divisorsAntidiagonal.mpr ⟨hd.symm, hn⟩))
      _ = 1 := if_pos rfl
  · rw [if_neg hsq]
    apply Finset.sum_eq_zero
    intro x hx
    apply if_neg
    intro he
    apply hsq
    refine ⟨x.1, ?_⟩
    simpa only [he] using (Nat.mem_divisorsAntidiagonal.mp hx).1.symm

private theorem integral_frozen_trace_smooth {Y n : ℕ}
    (hn : ∀ p ∈ n.primeFactors, p ≤ Y) :
    (∫ ω, steinhausDivisorTrace (frozenPrimePhase Y ω) n ∂steinhausMeasure) =
      divisorDiagonalMass n := by
  simp_rw [steinhausDivisorTrace_frozen_eq hn]
  exact integral_steinhausDivisorTrace n

private theorem integral_frozen_trace_large {Y p m : ℕ}
    (hp : p.Prime) (hpY : Y < p) (hm0 : 0 < m) (hmY : m < Y) :
    (∫ ω, steinhausDivisorTrace (frozenPrimePhase Y ω) (p * m) ∂steinhausMeasure) =
      -2 * divisorDiagonalMass m := by
  simp_rw [steinhausDivisorTrace_frozen_largePrime_mul hp hpY hm0 hmY]
  rw [integral_const_mul, integral_steinhausDivisorTrace]
  rfl

/-- The exact head mean is a smooth diagonal minus all large-prime diagonal channels. -/
theorem integral_frozenPrime_divisorHead (A : ℕ → ℂ) (N Y : ℕ)
    (hNY : N < Y * Y) :
    (∫ ω, ∑ n ∈ Finset.Icc 1 N,
      A n * steinhausDivisorTrace (frozenPrimePhase Y ω) n ∂steinhausMeasure) =
      (∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) N, A n * divisorDiagonalMass n) -
        2 * ∑ p ∈ largePrimes N Y, ∑ m ∈ Finset.Icc 1 (N / p),
          A (p * m) * divisorDiagonalMass m := by
  rw [integral_finsetSum _ (fun n _ => (integrable_frozenPrime_divisorTrace Y n).const_mul _)]
  simp_rw [integral_const_mul]
  rw [sum_Icc_eq_smooth_add_largePrimeSigma _ N Y hNY, Finset.sum_sigma]
  have hs : (∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) N,
      A n * ∫ ω, steinhausDivisorTrace (frozenPrimePhase Y ω) n ∂steinhausMeasure) =
      ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) N, A n * divisorDiagonalMass n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_frozen_trace_smooth (mem_smoothUpTo_iff.mp hn).2]
  rw [hs]
  have hl : (∑ p ∈ largePrimes N Y, ∑ m ∈ Finset.Icc 1 (N / p),
      A (p * m) * ∫ ω,
        steinhausDivisorTrace (frozenPrimePhase Y ω) (p * m) ∂steinhausMeasure) =
      -2 * ∑ p ∈ largePrimes N Y, ∑ m ∈ Finset.Icc 1 (N / p),
        A (p * m) * divisorDiagonalMass m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨⟨_, hpprime⟩, hpY⟩ := mem_largePrimes.mp hp
    have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
    rw [integral_frozen_trace_large hpprime hpY hm0
      (steinhausLargePrimeChannel_cofactor_lt hNY hp hm)]
    ring
  rw [hl]
  ring

/-- Equal divisor pairs reindex exactly by the positive square roots below the cutoff. -/
theorem sum_Icc_divisorDiagonalMass (A : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, A n * divisorDiagonalMass n) =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ^ 2 ≤ N), A (d ^ 2) := by
  classical
  have he : (∑ n ∈ Finset.Icc 1 N, A n * divisorDiagonalMass n) =
      ∑ n ∈ (Finset.Icc 1 N).filter IsSquare, A n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    rw [divisorDiagonalMass_eq_squareIndicator
      (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1), squareIndicator]
    simp only [mul_ite, mul_one, mul_zero]
  rw [he]
  symm
  apply Finset.sum_bij (fun d _ => d ^ 2)
  · intro d hd
    obtain ⟨hdI, hdN⟩ := Finset.mem_filter.mp hd
    have hd1 := (Finset.mem_Icc.mp hdI).1
    have hd2 : 1 ≤ d ^ 2 := by
      simpa only [pow_two, one_mul] using Nat.mul_le_mul hd1 hd1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd2, hdN⟩, ⟨d, pow_two d⟩⟩
  · intro d _ e _ hde
    exact Nat.pow_left_injective (by norm_num) hde
  · intro n hn
    obtain ⟨hnI, d, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
    have hdpos : 0 < d := by
      by_contra h
      have hz : d = 0 := by omega
      rw [hz] at hd
      norm_num at hd
      omega
    rw [hd] at hnN
    have hdN : d ≤ N := (Nat.le_mul_of_pos_right d hdpos).trans hnN
    refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hdN⟩,
      by simpa only [pow_two] using hnN⟩, ?_⟩
    simpa only [pow_two] using hd.symm
  · intro d _
    rfl

private theorem smooth_diagonal_eq_full (A : ℕ → ℂ) {N Y : ℕ} (hNY : N < Y * Y) :
    (∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) N, A n * divisorDiagonalMass n) =
      ∑ n ∈ Finset.Icc 1 N, A n * divisorDiagonalMass n := by
  classical
  apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr (mem_smoothUpTo_iff.mp hn).1)
  intro n hn hnnot
  have hnI := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hnI.1
  by_cases hsq : IsSquare n
  · exfalso
    obtain ⟨d, hd⟩ := hsq
    have hdpos : 0 < d := by
      by_contra h
      have hz : d = 0 := by omega
      rw [hz] at hd
      exact hn0 (by simpa using hd)
    have hdY : d < Y := by
      by_contra h
      have hYd : Y ≤ d := by omega
      have hprod := Nat.mul_le_mul hYd hYd
      have hdN : d * d ≤ N := by simpa only [hd] using hnI.2
      exact (not_le.mpr hNY) (hprod.trans hdN)
    apply hnnot
    apply mem_smoothUpTo_iff.mpr
    refine ⟨hnI, ?_⟩
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    rw [hd] at hdiv
    have hpd : p ∣ d := by
      rcases hprime.dvd_mul.mp hdiv with h | h <;> exact h
    exact (Nat.le_of_dvd hdpos hpd).trans hdY.le
  · rw [divisorDiagonalMass_eq_squareIndicator hn0, squareIndicator, if_neg hsq, mul_zero]

/-- The finite head average is the square diagonal minus the large-prime square channels. -/
theorem integral_frozenPrime_divisorHead_eq_squares (A : ℕ → ℂ) (N Y : ℕ)
    (hNY : N < Y * Y) :
    (∫ ω, ∑ n ∈ Finset.Icc 1 N,
      A n * steinhausDivisorTrace (frozenPrimePhase Y ω) n ∂steinhausMeasure) =
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ^ 2 ≤ N), A (d ^ 2)) -
        2 * ∑ p ∈ largePrimes N Y,
          ∑ d ∈ (Finset.Icc 1 (N / p)).filter (fun d => d ^ 2 ≤ N / p),
            A (p * d ^ 2) := by
  rw [integral_frozenPrime_divisorHead A N Y hNY, smooth_diagonal_eq_full A hNY,
    sum_Icc_divisorDiagonalMass A N]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact sum_Icc_divisorDiagonalMass (fun m => A (p * m)) (N / p)

end RHTower

