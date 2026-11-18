import GaloisForLFunctions.ExceptionalLayerTheory.PrimeDivisorsAtTheFirstDyadicSquareCrossing
import GaloisForLFunctions.ExceptionalLayerTheory.TheDirichletSeriesOfDyadicBinomialPrimeCounts
import GaloisForLFunctions.ExceptionalLayerTheory.DeepQuotientBlocksRecoverWeightedPrimeDivisors

/-!
# Distinct ordinary primes in dyadic binomial gcds

Every ordinary-prime carry supplies a prime divisor. Any additional factor
comes from a prime having at least two possible levels below the cutoff.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Ordinary primes in the last quotient class, each counted once. -/
def lastClassPrimes (q X : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter (fun p => q ∣ X/p+1)

/-- Exact positivity pattern of the prefix of the jump row. -/
theorem lastClassCoefficients_sum_eq {q : ℕ} (hq : 2≤q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, lastClassCoefficients q n = if q ∣ N+1 then 1 else 0 := by
  induction N with
  | zero =>
    have hn : ¬q ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
    simp [hn]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1≤N+1),ih]
    change _ + (if N+1=0 then (0:ℝ) else (if q ∣ N+1+1 then 1 else 0)-
      (if q ∣ N+1 then 1 else 0)) = _
    rw [if_neg (Nat.succ_ne_zero N)]
    ring

theorem quotientClassMassOf_eq_prefix (f : ArithmeticFunction ℝ) {q : ℕ} (hq : 2≤q) (X : ℕ) :
    quotientClassMassOf f q X=∑ n ∈ Icc 1 X, (f*lastClassCoefficients q) n := by
  rw [_root_.RHTower.sum_Icc_mul_apply,quotientClassMassOf]
  simp_rw [lastClassCoefficients_sum_eq hq]

/-- Weight one at each ordinary prime. -/
def lastClassOrdinaryPrimeIndicator : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Prime then 1 else 0,by simp [Nat.not_prime_zero]⟩

theorem lastClassPrimes_card (q X : ℕ) :
    ((lastClassPrimes q X).card : ℝ)=quotientClassMassOf lastClassOrdinaryPrimeIndicator q X := by
  rw [quotientClassMassOf,lastClassPrimes,Nat.primesLE_eq_filter_Icc_one,filter_filter,← sum_boole]
  refine sum_congr rfl fun p _ => ?_
  change (if p.Prime ∧ q∣X/p+1 then (1:ℝ) else 0) =
    (if p.Prime then 1 else 0)*(if q∣X/p+1 then 1 else 0)
  split_ifs <;> simp_all

private theorem lastClassPrimeIndicator_jump (q n : ℕ) :
    |(lastClassOrdinaryPrimeIndicator*lastClassCoefficients q) n| ≤ Real.log n/Real.log 2 := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  rw [ArithmeticFunction.mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal, vonMangoldt d.1/Real.log 2 := by
      refine sum_le_sum fun d _ => ?_
      have hinc : |lastClassCoefficients q d.2|≤1 := by
        change |if d.2=0 then (0:ℝ) else (if q∣d.2+1 then 1 else 0)-(if q∣d.2 then 1 else 0)|≤1
        split_ifs <;> norm_num
      rw [abs_mul]
      by_cases h : d.1.Prime
      · have hi : lastClassOrdinaryPrimeIndicator d.1=1 := if_pos h
        rw [hi,abs_one,one_mul,vonMangoldt_apply_prime h]
        exact hinc.trans ((one_le_div h2).mpr (Real.log_le_log (by norm_num) (by exact_mod_cast h.two_le)))
      · have hi : lastClassOrdinaryPrimeIndicator d.1=0 := if_neg h
        rw [hi,abs_zero,zero_mul]
        exact div_nonneg vonMangoldt_nonneg h2.le
    _ = _ := by rw [← sum_div,Nat.sum_divisorsAntidiagonal (fun a _ => (vonMangoldt a : ℝ)),vonMangoldt_sum]

/-- Moving the cutoff changes the ordinary count only at prime divisors of
the crossed integers. Each such divisor contributes at most one. -/
theorem lastClassPrimes_cutoff_gap {q M X : ℕ} (hq : 2≤q) (hMX : M≤X) :
    |((lastClassPrimes q X).card:ℝ)-((lastClassPrimes q M).card:ℝ)| ≤
      (X-M:ℕ)*(Real.log ((X:ℝ)+1)/Real.log 2) := by
  rw [lastClassPrimes_card,lastClassPrimes_card,quotientClassMassOf_eq_prefix _ hq,
    quotientClassMassOf_eq_prefix _ hq,← Ico_add_one_right_eq_Icc 1 X,← Ico_add_one_right_eq_Icc 1 M,
    ← sum_Ico_consecutive (lastClassOrdinaryPrimeIndicator*lastClassCoefficients q) (by omega : 1≤M+1) (by omega : M+1≤X+1),
    add_sub_cancel_left]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Ico (M+1) (X+1), Real.log ((X:ℝ)+1)/Real.log 2 := by
      refine sum_le_sum fun n hn => (lastClassPrimeIndicator_jump q n).trans ?_
      have hn0 : 0<n := by have := (mem_Ico.mp hn).1; omega
      exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hn0)
        (by exact_mod_cast (mem_Ico.mp hn).2.le)) (Real.log_nonneg (by norm_num))
    _ = _ := by simp

private theorem carry_one_dvd_gcd {j N p : ℕ} (hp : p.Prime)
    (hc : dyadicQuotientCarry j N p=1) : p ∈ (dyadicBinomialGcd j N).primeFactors := by
  let K := p.log (2^(j+1)*N)+2
  have hK : 2≤K := Nat.le_add_left ..
  have he := (dyadicBinomialGcd_carry_bounds j N hp hK
    (show p.log (2^(j+1)*N)<K by dsimp only [K]; omega)).1
  have h₁ : dyadicQuotientCarry j N p ≤ ∑ r ∈ Ico 1 K, dyadicQuotientCarry j N (p^r) := by
    simpa only [pow_one] using single_le_sum (f := fun r => dyadicQuotientCarry j N (p^r))
      (fun _ _ => Nat.zero_le _) (show 1 ∈ Ico 1 K from mem_Ico.mpr ⟨le_rfl,hK⟩)
  rw [hc] at h₁
  rw [← Nat.support_factorization,Finsupp.mem_support_iff]
  exact Nat.ne_of_gt (h₁.trans he)

/-- The set omitted by using only the prime level is confined to the square-root cutoff. -/
theorem dyadicBinomialGcd_distinct_prime_factors (j N : ℕ) :
    let q := 2^(j+1)
    lastClassPrimes q (q*N) ⊆ (dyadicBinomialGcd j N).primeFactors ∧
      (dyadicBinomialGcd j N).primeFactors ⊆ lastClassPrimes q (q*N) ∪ Nat.primesLE (q*N).sqrt := by
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  constructor
  · intro p hp
    obtain ⟨hpr,hd⟩ := mem_filter.mp hp
    exact carry_one_dvd_gcd (Nat.prime_of_mem_primesLE hpr) (if_pos hd)
  · intro p hp
    have hpr := (Nat.mem_primeFactors.mp hp).1
    by_cases hs : p≤(q*N).sqrt
    · exact mem_union_right _ (Nat.mem_primesLE.mpr ⟨hs,hpr⟩)
    · apply mem_union_left
      have hsq : q*N<p^2 := lt_of_not_ge (fun h => hs (Nat.le_sqrt.mpr (by simpa only [sq] using h)))
      have he := factorization_dyadicBinomialGcd_of_lt_sq (j := j) (N := N) hpr hsq
      rw [← Nat.support_factorization,Finsupp.mem_support_iff,he] at hp
      have hd : q ∣ q*N/p+1 := by
        by_contra hh
        exact hp (if_neg hh)
      have hx : p≤q*N := by
        by_contra! h
        rw [Nat.div_eq_of_lt h,zero_add] at hd
        have := Nat.le_of_dvd one_pos hd
        omega
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hx,hpr⟩,hd⟩

/-- Uniform count discrepancy, with the ordinary prime-counting function as
the exact available small-prime allowance. -/
theorem dyadicBinomialGcd_distinct_prime_count_error (j N : ℕ) :
    let X := 2^(j+1)*N
    0 ≤ ((dyadicBinomialGcd j N).primeFactors.card : ℝ)-(lastClassPrimes (2^(j+1)) X).card ∧
      ((dyadicBinomialGcd j N).primeFactors.card : ℝ)-(lastClassPrimes (2^(j+1)) X).card ≤
        Nat.primeCounting X.sqrt := by
  obtain ⟨hl,hu⟩ := dyadicBinomialGcd_distinct_prime_factors j N
  exact ⟨sub_nonneg.mpr (by exact_mod_cast card_le_card hl),sub_le_iff_le_add'.mpr (by
    have h := (card_le_card hu).trans (card_union_le ..)
    rw [Nat.primesLE_card_eq_primeCounting] at h
    exact_mod_cast h)⟩

#print axioms dyadicBinomialGcd_distinct_prime_factors
#print axioms dyadicBinomialGcd_distinct_prime_count_error

end GaloisForLFunctions.ExceptionalLayerTheory
