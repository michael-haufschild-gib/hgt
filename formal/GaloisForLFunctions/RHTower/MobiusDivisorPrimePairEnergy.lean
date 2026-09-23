import GaloisForLFunctions.RHTower.DivisorUnsignedChannelPositivity
import GaloisForLFunctions.RHTower.Sieve.CoprimeMoebiusSeries
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
/-!
# Actual first-prime contraction of divisor channels

Prime pairing preserves the complete signed sum and releases exactly twice
the actual unsigned overlap. All-cutoff unsigned positivity makes every first
prime pairing contract the diagonal, with no aggregate cancellation premise.
-/

noncomputable section
open Finset
namespace RHTower

private theorem unsigned_channel_zero_above {M d : ℕ} (h : M<d) :
    divisorUnsignedDilationChannel M d=0 := by
  simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<d)]

private theorem finite_prime_pair_sum (f : ℕ → ℝ) (M p : ℕ) (hp : 0<p)
    (hz : ∀ d, M<d → f d=0) (hpp : ∀ d, p∣d → f (p*d)=0) :
    (∑ d ∈ Icc 1 M, f d) = ∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d), (f d+f (p*d)) := by
  have hmul : (∑ d ∈ (Icc 1 M).filter (fun d => p∣d), f d) =
      ∑ d ∈ Icc 1 M, f (p*d) := by
    rw [sum_Icc_filter_dvd_reindex p M hp]
    apply sum_subset
    · intro d hd
      exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (Nat.div_le_self M p)⟩
    · intro d hd hnot
      have hlt : M/p<d := by have := mem_Icc.mp hd; simp only [mem_Icc] at hnot; omega
      have hprod : M<p*d := by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hp).mp hlt
      exact hz _ hprod
  have hfree : (∑ d ∈ Icc 1 M, f (p*d)) =
      ∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d), f (p*d) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases h : p∣d
    · simp [h,hpp d h]
    · simp [h]
  have hsplit := sum_filter_add_sum_filter_not (s := Icc 1 M) (p := fun d => p∣d) (f := f)
  rw [sum_add_distrib,← hfree,← hmul]
  linarith only [hsplit]

/-- The actual signed pair after eliminating one prime from the cofactor labels. -/
def mobiusDivisorPrimePair (M p d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d:ℤ):ℝ)*
    (divisorUnsignedDilationChannel M d-divisorUnsignedDilationChannel M (p*d))

/-- Exact first-prime pairing preserves the complete arithmetic signed sum. -/
theorem sum_mobiusDivisorPrimePair {p : ℕ} (hp : p.Prime) (M : ℕ) :
    (∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d), mobiusDivisorPrimePair M p d) =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
  have hz (d : ℕ) (hd : M<d) : mobiusDivisorDilationChannel M d=0 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,unsigned_channel_zero_above hd,mul_zero]
  have hpp (d : ℕ) (hd : p∣d) : mobiusDivisorDilationChannel M (p*d)=0 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,Sieve.moebius_prime_mul hp,if_pos hd,zero_mul]
  rw [finite_prime_pair_sum _ M p hp.pos hz hpp]
  apply sum_congr rfl
  intro d hd
  have hpd := (mem_filter.mp hd).2
  rw [mobiusDivisorPrimePair,mobiusDivisorDilationChannel_eq_moebius_unsigned,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,Sieve.moebius_prime_mul hp,if_neg hpd]
  ring

/-- Exact energy released by one prime pair, retaining its actual source overlap. -/
theorem sum_mobiusDivisorPrimePair_sq_eq {p : ℕ} (hp : p.Prime) (M : ℕ) :
    (∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d), (mobiusDivisorPrimePair M p d)^(2 : ℕ)) =
      (∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d)^(2 : ℕ))-
        2*∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d),
          (((ArithmeticFunction.moebius d:ℤ):ℝ)^(2 : ℕ)*
            divisorUnsignedDilationChannel M d*divisorUnsignedDilationChannel M (p*d)) := by
  have hz (d : ℕ) (hd : M<d) : (mobiusDivisorDilationChannel M d)^(2 : ℕ)=0 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,unsigned_channel_zero_above hd,mul_zero]
    norm_num
  have hpp (d : ℕ) (hd : p∣d) : (mobiusDivisorDilationChannel M (p*d))^(2 : ℕ)=0 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,Sieve.moebius_prime_mul hp,if_pos hd,zero_mul]
    norm_num
  rw [finite_prime_pair_sum _ M p hp.pos hz hpp,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  have hpd := (mem_filter.mp hd).2
  rw [mobiusDivisorPrimePair,mobiusDivisorDilationChannel_eq_moebius_unsigned,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,Sieve.moebius_prime_mul hp,if_neg hpd]
  ring

/-- Every prime gives unconditional first-pair contraction of the literal arithmetic diagonal. -/
theorem sum_mobiusDivisorPrimePair_sq_le {p : ℕ} (hp : p.Prime) (M : ℕ) :
    (∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d), (mobiusDivisorPrimePair M p d)^(2 : ℕ)) ≤
      ∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d)^(2 : ℕ) := by
  rw [sum_mobiusDivisorPrimePair_sq_eq hp]
  have h : 0 ≤ ∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d),
      (((ArithmeticFunction.moebius d:ℤ):ℝ)^(2 : ℕ)*
        divisorUnsignedDilationChannel M d*divisorUnsignedDilationChannel M (p*d)) :=
    sum_nonneg (fun d _ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (divisorUnsignedDilationChannel_nonneg M d))
      (divisorUnsignedDilationChannel_nonneg M (p*d)))
  linarith only [h]
end RHTower
