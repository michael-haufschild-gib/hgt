import GaloisForLFunctions.ExceptionalLayerTheory.DistinctPrimeFactorsInDyadicBinomialGcds
import GaloisForLFunctions.RHTower.Sieve.LocalEulerConstruction
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The factorial weight in an ordinary-prime quotient sum

A prime of multiplicity k acquires weight (-1)^k/k!. Removing one
copy multiplies the weight by minus its multiplicity. Dividing also
by the total number of factors makes the sum over removed primes exact.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The multiplicative weight with local coefficients (-1)^k/k!. -/
def factorialParityWeight : ArithmeticFunction ℝ :=
  localEuler (fun _ k => (-1:ℝ)^k/(k.factorial:ℝ))

/-- The coefficient whose convolution with the ordinary prime indicator removes the unit term. -/
def dividedFactorialParityWeight : ArithmeticFunction ℝ :=
  ⟨fun n => factorialParityWeight n/((Ω n:ℝ)+1),by simp⟩

/-- Local coefficients on every prime power, including the unit. -/
theorem factorialParityWeight_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    factorialParityWeight (p^k)=(-1:ℝ)^k/(k.factorial:ℝ) := by
  rw [factorialParityWeight,localEuler_prime_pow _ (⟨p,hp⟩:Nat.Primes) k]
  split_ifs with h
  · simp [h]
  · rfl

private theorem factorialParityWeight_remove {m p : ℕ} (hp : p.Prime) (hm : m≠0) :
    factorialParityWeight m = -((m.factorization p:ℝ)+1)*factorialParityWeight (p*m) := by
  let k := m.factorization p
  let u := m/p^k
  have he : p^k*u=m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hc : p.Coprime u := Nat.coprime_ordCompl hp hm
  have hmult := localEuler_isMultiplicative (fun _ k => (-1:ℝ)^k/(k.factorial:ℝ))
  have h (j : ℕ) : factorialParityWeight (p^j*u)=(-1:ℝ)^j/(j.factorial:ℝ)*factorialParityWeight u := by
    calc
      _ = factorialParityWeight (p^j)*factorialParityWeight u := hmult.map_mul_of_coprime (hc.pow_left j)
      _ = _ := by rw [factorialParityWeight_pow hp]
  have hm' := h k
  rw [he] at hm'
  have hpm := h (k+1)
  rw [pow_succ',mul_assoc,he] at hpm
  rw [hm',hpm,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  change _ = -((k:ℝ)+1)*_
  have hpos : (0:ℝ)<(k:ℝ)+1 := by positivity
  field_simp [hpos.ne']

/-- Convolving the divided weight with the genuine prime indicator cancels the
total number of prime factors, with multiplicity, at every positive integer. -/
theorem ordinaryPrimeIndicator_mul_dividedFactorialParityWeight :
    lastClassOrdinaryPrimeIndicator*dividedFactorialParityWeight=1-factorialParityWeight := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · change (lastClassOrdinaryPrimeIndicator*dividedFactorialParityWeight) 1 =
      (1:ArithmeticFunction ℝ) 1-factorialParityWeight 1
    simp [lastClassOrdinaryPrimeIndicator,Nat.not_prime_one,factorialParityWeight]
  have hΩ : 0<(Ω n:ℝ) := by exact_mod_cast cardFactors_pos_iff_one_lt.mpr (show 1<n by omega)
  have hpSet : n.divisors.filter Nat.Prime=n.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_divisors,Nat.mem_primeFactors]
    tauto
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal
    (fun p m => lastClassOrdinaryPrimeIndicator p*dividedFactorialParityWeight m)]
  have hsum : (∑ p ∈ n.divisors, lastClassOrdinaryPrimeIndicator p*dividedFactorialParityWeight (n/p)) =
      ∑ p ∈ n.primeFactors, dividedFactorialParityWeight (n/p) := by
    rw [← hpSet,sum_filter]
    refine sum_congr rfl fun p _ => ?_
    change (if p.Prime then (1:ℝ) else 0)*_=_
    split <;> simp_all
  rw [hsum]
  calc
    _ = ∑ p ∈ n.primeFactors, (n.factorization p:ℝ)*(-factorialParityWeight n/(Ω n:ℝ)) := by
      refine sum_congr rfl fun p hpn => ?_
      obtain ⟨hp,hpd,_⟩ := Nat.mem_primeFactors.mp hpn
      have hpm : p*(n/p)=n := Nat.mul_div_cancel' hpd
      have hm : n/p≠0 := Nat.ne_of_gt ((Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd hn hpd))
      have hw := factorialParityWeight_remove hp hm
      rw [hpm] at hw
      have hmΩ := cardFactors_mul hp.ne_zero hm
      rw [hpm,cardFactors_apply_prime hp] at hmΩ
      have hfac := congrArg (fun k : ℕ => k.factorization p) hpm
      simp only [Nat.factorization_mul hp.ne_zero hm,Finsupp.add_apply,hp.factorization_self] at hfac
      change factorialParityWeight (n/p)/((Ω (n/p):ℝ)+1)=_
      rw [hw,hmΩ,← hfac]
      push_cast
      ring
    _ = _ := by
      rw [← sum_mul,← Nat.cast_sum]
      have hfac : ∑ p ∈ n.primeFactors, n.factorization p=Ω n := by
        rw [cardFactors_eq_sum_factorization,Finsupp.sum,Nat.support_factorization]
      rw [hfac]
      change _ = (1:ArithmeticFunction ℝ) n-factorialParityWeight n
      rw [ArithmeticFunction.one_apply_ne hn1,zero_sub]
      field_simp [hΩ.ne']

/-- Each local factorial denominator has modulus at least one. -/
theorem abs_factorialParityWeight_le_one (n : ℕ) : |factorialParityWeight n|≤1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  change |if n=0 then (0:ℝ) else ∏ p ∈ n.primeFactors, (-1:ℝ)^(n.factorization p)/((n.factorization p).factorial:ℝ)|≤1
  rw [if_neg hn.ne',abs_prod]
  apply prod_le_one (fun _ _ => abs_nonneg _)
  intro p _
  rw [abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_nonneg (Nat.cast_nonneg _)]
  exact (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.factorial_pos _)

/-- Dividing by one plus the number of prime factors preserves the unit bound. -/
theorem abs_dividedFactorialParityWeight_le_one (n : ℕ) : |dividedFactorialParityWeight n|≤1 := by
  have hw := abs_factorialParityWeight_le_one n
  change |factorialParityWeight n/((Ω n:ℝ)+1)|≤1
  rw [abs_div,abs_of_nonneg (by positivity : 0≤(Ω n:ℝ)+1)]
  exact (div_le_one (by positivity)).mpr (hw.trans (le_add_of_nonneg_left (Nat.cast_nonneg _)))

/-- Exact prime quotient realization of the complementary factorial-weighted parity sum. -/
theorem prime_sum_dividedFactorialParityWeight {N : ℕ} (hN : 1≤N) :
    (∑ p ∈ Nat.primesLE N, ∑ m ∈ Icc 1 (N/p), dividedFactorialParityWeight m) =
      1-∑ n ∈ Icc 1 N, factorialParityWeight n := by
  calc
    _ = ∑ n ∈ Icc 1 N, (lastClassOrdinaryPrimeIndicator*dividedFactorialParityWeight) n := by
      rw [_root_.RHTower.sum_Icc_mul_apply,Nat.primesLE_eq_filter_Icc_one,sum_filter]
      refine sum_congr rfl fun p _ => ?_
      change (if p.Prime then _ else 0)=(if p.Prime then (1:ℝ) else 0)*_
      split <;> simp_all
    _ = _ := by
      rw [ordinaryPrimeIndicator_mul_dividedFactorialParityWeight]
      change ∑ n ∈ Icc 1 N, ((1:ArithmeticFunction ℝ) n-factorialParityWeight n)=_
      rw [sum_sub_distrib]
      congr 1
      rw [sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hN⟩)]
      · simp
      · intro n _ hn; exact ArithmeticFunction.one_apply_ne hn

#print axioms ordinaryPrimeIndicator_mul_dividedFactorialParityWeight
#print axioms prime_sum_dividedFactorialParityWeight

end GaloisForLFunctions.ExceptionalLayerTheory
