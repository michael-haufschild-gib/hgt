import GaloisForLFunctions.ExceptionalLayerTheory.PrimeDivisorsAtTheFirstDyadicSquareCrossing
import GaloisForLFunctions.ExceptionalLayerTheory.ThePrimeCountInADyadicBinomialGcd

/-!
# A depth-independent bound for dyadic binomial gcds

All excess over the selected prime powers comes from small primes or two
adjacent integers above a quotient of the base cutoff. Bounding each
valuation in the first binomial removes the final dyadic width from the
error. Beyond the base cutoff the selected mass itself vanishes.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def candidatePrimes (N : ℕ) : Finset ℕ :=
  range ((2*N).sqrt+1) ∪ (range (N.sqrt+2)).image (fun k => N/k+1) ∪
    (range (N.sqrt+2)).image (fun k => N/k+2)

private theorem card_candidates (N : ℕ) :
    (candidatePrimes N).card ≤ (2*N).sqrt+1+2*(N.sqrt+2) := by
  unfold candidatePrimes
  calc
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_union_le _ _) card_image_le
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_left card_image_le _) _
    _ = _ := by simp only [card_range]; omega

private theorem first_valuation_bound (j N : ℕ) {p : ℕ} (hp : p.Prime) (hN : 0 < N) :
    ((dyadicBinomialGcd j N).factorization p : ℝ)*Real.log p ≤ Real.log (2*(N:ℝ)+2) := by
  have hv := Nat.factorization_le_factorization_of_dvd_right (a := p)
    (dyadicBinomialGcd_dvd_first j N) (dyadicBinomialGcd_pos j N).ne' (Nat.centralBinom_pos N).ne'
  rw [Nat.centralBinom_eq_two_mul_choose] at hv
  have hpow := (pow_le_pow_right₀ hp.one_le hv).trans
    (Nat.pow_factorization_choose_le (by omega : 0 < 2*N))
  have hreal : (p:ℝ) ^ (dyadicBinomialGcd j N).factorization p ≤ 2*(N:ℝ)+2 := by
    exact_mod_cast hpow.trans (Nat.le_add_right (2*N) 2)
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _) hreal

/-- The log-gcd error has square-root size up to a logarithm, uniformly in the dyadic depth. -/
theorem dyadicBinomialGcd_log_excess_uniform_in_depth (j N : ℕ) :
    Real.log (dyadicBinomialGcd j N) - dyadicCommonPrimeMass j N ≤
      (((2*N).sqrt+1+2*(N.sqrt+2) : ℕ) : ℝ)*Real.log (2*(N:ℝ)+2) := by
  let X := 2^(j+1)*N
  let L := Real.log (2*(N:ℝ)+2)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  let S := candidatePrimes N
  rw [log_dyadicBinomialGcd_eq_sum_primes,dyadicCommonPrimeMass_eq_sum_levels,← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE X, if p ∈ S then L else 0 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hX,hp'⟩ := Nat.mem_primesLE.mp hp
      have hN : 0 < N := by
        by_contra! h
        simp only [Nat.eq_zero_of_le_zero h,mul_zero] at hX
        exact hp'.pos.not_ge hX
      have hlog := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast hp'.one_le)
      have hpos : 0 ≤ (dyadicCommonCarryLevels j N p : ℝ)*Real.log p :=
        mul_nonneg (Nat.cast_nonneg _) hlog
      split_ifs with hc
      · exact (sub_le_self _ hpos).trans (first_valuation_bound j N hp' hN)
      by_cases hv : (dyadicBinomialGcd j N).factorization p = 0
      · simpa only [hv,Nat.cast_zero,zero_mul,zero_sub,neg_nonpos] using hpos
      have hsmall : 2*N < p^2 := by
        by_contra! h
        have hs := Nat.le_sqrt.mpr (by simpa only [sq] using h : p*p ≤ 2*N)
        exact hc (mem_union_left _ (mem_union_left _ (mem_range.mpr (by omega))))
      have hlarge : X < p^2 := by
        by_contra! h
        obtain ⟨k,hk,hl,hu⟩ := exists_small_quotient_of_common_prime hp' hsmall j
          (Nat.pos_of_ne_zero hv) h
        have hk' : k ∈ range (N.sqrt+2) := mem_range.mpr (by have := (mem_Icc.mp hk).2; omega)
        rcases (show p = N/k+1 ∨ p = N/k+2 by omega) with e | e
        · exact hc (mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨k,hk',e.symm⟩)))
        · exact hc (mem_union_right _ (mem_image.mpr ⟨k,hk',e.symm⟩))
      rw [factorization_dyadicBinomialGcd_of_lt_sq hp' hlarge,sub_nonpos]
      apply mul_le_mul_of_nonneg_right _ hlog
      have h1 : 1 ≤ p.log X := Nat.le_log_of_pow_le hp'.one_lt (by simpa using hX)
      exact_mod_cast (show dyadicQuotientCarry j N p ≤ dyadicCommonCarryLevels j N p by
        simpa only [pow_one] using (single_le_sum (f := fun r => dyadicQuotientCarry j N (p^r))
          (fun _ _ => Nat.zero_le _) (mem_Icc.mpr ⟨le_rfl,h1⟩)))
    _ = (((Nat.primesLE X).filter (· ∈ S)).card : ℝ)*L := by
      rw [← sum_filter,sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hL
      exact_mod_cast (card_le_card (show (Nat.primesLE X).filter (· ∈ S) ⊆ S from
        fun p hp => (mem_filter.mp hp).2)).trans (card_candidates N)

/-- If the width exceeds the base by at least two, no divisor gives a common carry. -/
theorem dyadicCommonPrimeMass_eq_zero_of_deep {j N : ℕ} (hd : N+1 < 2^(j+1)) :
    dyadicCommonPrimeMass j N = 0 := by
  apply sum_eq_zero
  intro m hm
  suffices h : dyadicQuotientCarry j N m = 0 by rw [h,Nat.cast_zero,zero_mul]
  by_contra! hn
  have hone : dyadicQuotientCarry j N m = 1 := by
    unfold dyadicQuotientCarry at *; split <;> simp_all
  obtain ⟨k,hk,hu⟩ := (dyadicQuotientCarry_one_iff (mem_Icc.mp hm).1).mp hone
  let q := 2^(j+1)
  change q*(k*m) ≤ q*N+m at hu
  change N+1 < q at hd
  have hlo := (Nat.mul_le_mul_left q (show N+1 ≤ k*m from hk)).trans hu
  rw [mul_add,mul_one] at hlo
  have hqm : q ≤ m := by omega
  have hkpos : 0 < k := by by_contra! e; simp [Nat.eq_zero_of_le_zero e] at hk
  have hump := (Nat.mul_le_mul_left q (Nat.le_mul_of_pos_left m hkpos)).trans hu
  have hq : q-1+1 = q := by omega
  have hstep : q*N < (q-1)*m := calc
    q*N < q*(q-1) := (Nat.mul_lt_mul_left (by omega)).mpr (by omega)
    _ = (q-1)*q := mul_comm _ _
    _ ≤ (q-1)*m := Nat.mul_le_mul_left _ hqm
  nth_rw 1 [← hq] at hump
  rw [add_mul,one_mul] at hump
  omega

/-- At every sufficiently deep intersection the entire logarithm satisfies the uniform bound. -/
theorem deep_dyadicBinomialGcd_log_bound {j N : ℕ} (hd : N+1 < 2^(j+1)) :
    Real.log (dyadicBinomialGcd j N) ≤
      (((2*N).sqrt+1+2*(N.sqrt+2) : ℕ) : ℝ)*Real.log (2*(N:ℝ)+2) := by
  simpa only [dyadicCommonPrimeMass_eq_zero_of_deep hd,sub_zero] using
    dyadicBinomialGcd_log_excess_uniform_in_depth j N

#print axioms dyadicBinomialGcd_log_excess_uniform_in_depth
#print axioms deep_dyadicBinomialGcd_log_bound

end GaloisForLFunctions.ExceptionalLayerTheory
