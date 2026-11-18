import GaloisForLFunctions.ExceptionalLayerTheory.CommonCarriesOfDyadicCentralBinomialCoefficients
import Mathlib.Data.Nat.Sqrt

/-!
# Prime divisors at the first dyadic square crossing

If the sequence of doubled cutoffs passes the square of a common prime,
use its last cutoff below that square. The single carry there forces the
prime to lie among two integers immediately above a quotient of the base
cutoff. The number of candidates is independent of the final depth.
-/

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A common carry means the next multiple of the divisor is within one
divisor-length of the cutoff and has the prescribed quotient. -/
theorem dyadicQuotientCarry_one_iff {j N m : ℕ} (hm : 0 < m) :
    dyadicQuotientCarry j N m = 1 ↔ ∃ k : ℕ, N < k*m ∧
      2^(j+1)*(k*m) ≤ 2^(j+1)*N + m := by
  let q := 2^(j+1)
  have hq : 0 < q := pow_pos two_pos _
  have hi : dyadicQuotientCarry j N m = 1 ↔ q ∣ q*N/m+1 := by
    unfold dyadicQuotientCarry
    split <;> simp_all [q]
  rw [hi]
  constructor
  · rintro ⟨k,hk⟩
    have hl := (Nat.div_lt_iff_lt_mul hm).mp (show q*N/m < q*N/m+1 by omega)
    rw [hk,mul_assoc] at hl
    refine ⟨k,(Nat.mul_lt_mul_left hq).mp hl,?_⟩
    change q*(k*m) ≤ q*N+m
    rw [← mul_assoc,← hk,add_mul,one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  · rintro ⟨k,hl,hu⟩
    change q*(k*m) ≤ q*N+m at hu
    have hlt : q*N < (q*k)*m := by
      rw [mul_assoc]
      exact (Nat.mul_lt_mul_left hq).mpr hl
    have hlo := (Nat.div_lt_iff_lt_mul hm).mpr hlt
    have hhi : q*k ≤ (q*N+m)/m := (Nat.le_div_iff_mul_le hm).mpr (by rwa [mul_assoc])
    rw [Nat.add_div_right _ hm] at hhi
    exact ⟨k,by omega⟩

theorem dyadicBinomialGcd_dvd_first (j N : ℕ) :
    dyadicBinomialGcd j N ∣ Nat.centralBinom N := by
  induction j with
  | zero => exact dvd_refl _
  | succ j ih => exact (Nat.gcd_dvd_left _ _).trans ih

/-- A prime surviving the first crossing of its square lies one or two units
above `N/k`, for some `k` no larger than the square root of `N` plus one. -/
theorem exists_small_quotient_of_common_prime {N p : ℕ} (hp : p.Prime) (hfirst : 2*N < p^2)
    (j : ℕ) : 0 < (dyadicBinomialGcd j N).factorization p → p^2 ≤ 2^(j+1)*N →
    ∃ k ∈ Icc 1 (N.sqrt+1), N/k < p ∧ p ≤ N/k+2 := by
  induction j with
  | zero => intro _ ht; simp only [Nat.zero_add,pow_one] at ht; omega
  | succ j ih =>
    intro hval hlast
    let q := 2^(j+1)
    have hq : 0 < q := pow_pos two_pos _
    have hprev : 0 < (dyadicBinomialGcd j N).factorization p :=
      hval.trans_le (Nat.factorization_le_factorization_of_dvd_right (Nat.gcd_dvd_left _ _)
        (dyadicBinomialGcd_pos (j+1) N).ne' (dyadicBinomialGcd_pos j N).ne')
    rcases le_or_gt (p^2) (q*N) with h | h
    · exact ih hprev h
    have hbit := factorization_dyadicBinomialGcd_of_lt_sq hp h
    have hcarry : dyadicQuotientCarry j N p = 1 := by
      rw [hbit] at hprev
      unfold dyadicQuotientCarry at *
      split at hprev <;> simp_all
    obtain ⟨k,hl,hu⟩ := dyadicQuotientCarry_one_iff hp.pos |>.mp hcarry
    change q*(k*p) ≤ q*N+p at hu
    have hk : 0 < k := by by_contra! h; rw [Nat.eq_zero_of_le_zero h,zero_mul] at hl; omega
    have hcross : p*p ≤ 2*(q*N) := by
      simpa only [sq,pow_succ (2:ℕ) (j+1),mul_comm (2^(j+1)) 2,mul_assoc,q] using hlast
    have hpcheap : p < q*(2*k) := Nat.lt_of_mul_lt_mul_right (calc
      p*p ≤ 2*(q*N) := hcross
      _ < 2*(q*(k*p)) := (Nat.mul_lt_mul_left two_pos).mpr ((Nat.mul_lt_mul_left hq).mpr hl)
      _ = (q*(2*k))*p := by ring)
    have hclose : k*p ≤ N+2*k := le_of_lt ((Nat.mul_lt_mul_left hq).mp (calc
      q*(k*p) ≤ q*N+p := hu
      _ < q*N+q*(2*k) := Nat.add_lt_add_left hpcheap _
      _ = q*(N+2*k) := (mul_add ..).symm))
    have hkp : k*p ≤ N+p := Nat.le_of_mul_le_mul_left (calc
      q*(k*p) ≤ q*N+p := hu
      _ ≤ q*N+q*p := Nat.add_le_add_left (Nat.le_mul_of_pos_left p hq) _
      _ = q*(N+p) := (mul_add ..).symm) hq
    have hdiv : N/p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by
      rw [← sq]; omega)
    have hs : N/p ≤ N.sqrt := Nat.le_sqrt.mpr
      ((Nat.mul_le_mul_left (N/p) hdiv.le).trans (Nat.div_mul_le_self N p))
    have hk' := (Nat.le_div_iff_mul_le hp.pos).mpr hkp
    rw [Nat.add_div_right _ hp.pos] at hk'
    refine ⟨k,mem_Icc.mpr ⟨hk,by omega⟩,(Nat.div_lt_iff_lt_mul hk).mpr (by rwa [mul_comm]),?_⟩
    have hp' := (Nat.le_div_iff_mul_le hk).mpr (show p*k ≤ N+k*2 by
      simpa only [mul_comm p k,mul_comm k 2] using hclose)
    rwa [Nat.add_mul_div_left _ _ hk] at hp'

#print axioms exists_small_quotient_of_common_prime

end GaloisForLFunctions.ExceptionalLayerTheory
