import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Common carries of dyadic central binomial coefficients

A common binary digit of the quotients by a prime power contributes to the
gcd of consecutive central binomial coefficients. Valuations can also meet
at different powers of the same prime. Their excess is bounded by the
number of higher powers of that prime below the top cutoff.
-/

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Gcd of the first `j+1` central binomial coefficients at dyadic dilates of `N`. -/
def dyadicBinomialGcd : ℕ → ℕ → ℕ
  | 0, N => Nat.centralBinom N
  | j+1, N => (dyadicBinomialGcd j N).gcd (Nat.centralBinom (2^(j+1)*N))

/-- The last residue class of the quotient by `m` modulo the dyadic width. -/
def dyadicQuotientCarry (j N m : ℕ) : ℕ :=
  if 2^(j+1) ∣ 2^(j+1)*N/m+1 then 1 else 0

theorem dyadicBinomialGcd_pos (j N : ℕ) : 0 < dyadicBinomialGcd j N := by
  induction j with
  | zero => exact Nat.centralBinom_pos N
  | succ j ih => exact Nat.gcd_pos_of_pos_left _ ih

private def binomialCarry (n m : ℕ) := (2*n/m)%2

private theorem quotient_half (a m : ℕ) : (2*a/m)/2 = a/m := by
  rw [Nat.div_div_eq_div_mul,mul_comm m 2,Nat.mul_div_mul_left _ _ two_pos]

private theorem twice_dvd_succ (q t : ℕ) :
    2*q ∣ t+1 ↔ q ∣ t/2+1 ∧ t%2=1 := by
  constructor
  · rintro ⟨k,hk⟩
    rw [mul_assoc] at hk
    exact ⟨⟨k,by omega⟩,by omega⟩
  · rintro ⟨⟨k,hk⟩,ht⟩
    exact ⟨k,by rw [mul_assoc]; omega⟩

private theorem carry_zero (N m : ℕ) :
    dyadicQuotientCarry 0 N m = binomialCarry N m := by
  simp only [dyadicQuotientCarry,binomialCarry,Nat.zero_add,pow_one]
  split <;> omega

private theorem carry_succ (j N m : ℕ) :
    dyadicQuotientCarry (j+1) N m =
      min (dyadicQuotientCarry j N m) (binomialCarry (2^(j+1)*N) m) := by
  let q := 2^(j+1)
  have hpow : 2^(j+1+1) = 2*q := by rw [pow_succ, mul_comm]
  simp only [dyadicQuotientCarry,hpow,mul_assoc 2 q N,twice_dvd_succ,quotient_half,binomialCarry]
  change (if q ∣ q*N/m+1 ∧ (2*(q*N)/m)%2=1 then 1 else 0) =
    min (if q ∣ q*N/m+1 then 1 else 0) ((2*(q*N)/m)%2)
  split_ifs <;> omega

/-- Kummer's carry for a central binomial coefficient is the last bit of the quotient. -/
private theorem factorization_binomial_eq_sum {p n K : ℕ} (hp : p.Prime)
    (hK : Nat.log p (2*n) < K) :
    (Nat.centralBinom n).factorization p = ∑ r ∈ Ico 1 K, binomialCarry n (p^r) := by
  rw [two_mul] at hK
  rw [Nat.centralBinom_eq_two_mul_choose,two_mul,Nat.factorization_choose' hp hK]
  calc
    _ = ∑ r ∈ Ico 1 K, (if p^r ≤ n%p^r + n%p^r then 1 else 0 : ℕ) :=
      (sum_boole (R := ℕ) _ _).symm
    _ = _ := ?_
  refine sum_congr rfl fun r _ => ?_
  rw [binomialCarry,two_mul,Nat.add_div (pow_pos hp.pos _)]
  split <;> omega

private theorem single_valuation_upper {p n K : ℕ} (hp : p.Prime) (h2 : 2 ≤ K)
    (hK : Nat.log p (2*n) < K) :
    (Nat.centralBinom n).factorization p ≤ binomialCarry n p + (K-2) := by
  rw [factorization_binomial_eq_sum hp hK,sum_eq_sum_Ico_succ_bot (by omega : 1 < K),pow_one]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _r ∈ Ico 2 K, 1 := sum_le_sum fun _ _ => by unfold binomialCarry; omega
    _ = K-2 := by simp

/-- The gcd counts every common prime-power carry. Its valuation is at most
the common carry at the prime plus one for each possible higher power. -/
theorem dyadicBinomialGcd_carry_bounds (j N : ℕ) {p K : ℕ} (hp : p.Prime) (h2 : 2 ≤ K)
    (hK : Nat.log p (2^(j+1)*N) < K) :
    (∑ r ∈ Ico 1 K, dyadicQuotientCarry j N (p^r)) ≤ (dyadicBinomialGcd j N).factorization p ∧
    (dyadicBinomialGcd j N).factorization p ≤ dyadicQuotientCarry j N p + (K-2) := by
  induction j with
  | zero =>
    simp only [Nat.zero_add,pow_one] at hK
    simp only [dyadicBinomialGcd,carry_zero]
    exact ⟨(factorization_binomial_eq_sum hp hK).ge, single_valuation_upper hp h2 hK⟩
  | succ j ih =>
    let n := 2^(j+1)*N
    have htop : 2^(j+1+1)*N = 2*n := by rw [pow_succ, mul_comm (2^(j+1)) 2, mul_assoc]
    rw [htop] at hK
    have hn : Nat.log p n < K := (Nat.log_mono_right (show n ≤ 2*n by omega)).trans_lt hK
    obtain ⟨hlo,hhi⟩ := ih hn
    have hval := DFunLike.congr_fun (Nat.factorization_gcd (dyadicBinomialGcd_pos j N).ne'
      (Nat.centralBinom_pos n).ne') p
    change (dyadicBinomialGcd (j+1) N).factorization p =
      min ((dyadicBinomialGcd j N).factorization p) ((Nat.centralBinom n).factorization p) at hval
    simp only [hval,carry_succ]
    refine ⟨le_min ?_ ?_,?_⟩
    · exact (sum_le_sum fun r _ => min_le_left _ _).trans hlo
    · exact (sum_le_sum fun r _ => min_le_right _ _).trans_eq (factorization_binomial_eq_sum hp hK).symm
    · exact (min_le_min hhi (single_valuation_upper hp h2 hK)).trans_eq (min_add_add_right ..)

/-- Above the square root, the prime divides the gcd once precisely in the last quotient class. -/
theorem factorization_dyadicBinomialGcd_of_lt_sq {j N p : ℕ} (hp : p.Prime)
    (h : 2^(j+1)*N < p^2) :
    (dyadicBinomialGcd j N).factorization p = dyadicQuotientCarry j N p := by
  have hlog : Nat.log p (2^(j+1)*N) < 2 := by
    rcases Nat.eq_zero_or_pos (2^(j+1)*N) with h0 | hn
    · simp [h0]
    · exact Nat.log_lt_of_lt_pow hn.ne' h
  obtain ⟨hlo,hhi⟩ := dyadicBinomialGcd_carry_bounds j N hp (le_refl 2) hlog
  exact le_antisymm (by simpa using hhi) (by simpa using hlo)

#print axioms dyadicBinomialGcd_carry_bounds
#print axioms factorization_dyadicBinomialGcd_of_lt_sq

end GaloisForLFunctions.ExceptionalLayerTheory
