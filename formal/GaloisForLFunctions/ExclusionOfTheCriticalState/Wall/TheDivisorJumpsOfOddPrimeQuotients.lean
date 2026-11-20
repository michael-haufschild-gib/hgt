import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisor jumps of the odd-quotient prime excess

The sign character of a quotient changes at its denominator multiples.
At an even endpoint the new excess is the full divisor excess less twice
the divisor excess at the half endpoint. Dyadic inversion therefore recovers
the ordinary divisor reading from the odd-quotient increments.
-/

open Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
noncomputable section
open scoped Classical

/-- Signed change as the numerator reaches a positive integer. -/
def oddPrimeJump (S : Finset ℕ) (u : ℕ) : ℝ :=
  oddQuotientPrimeExcess S u - oddQuotientPrimeExcess S (u-1)

/-- Prime excess of the divisors of u retained by the denominator band. -/
def divisorPrimeExcess (S : Finset ℕ) (u : ℕ) : ℝ :=
  ∑ n ∈ S, if n ∣ u then ordinaryPrimeExcessCoeff n else 0

private theorem digit_jump (n H : ℕ) (a : ℝ) :
    (if (H+1)/n%2=1 then a else 0) - (if H/n%2=1 then a else 0) =
      (if n ∣ H+1 then a else 0) - 2*(if 2*n ∣ H+1 then a else 0) := by
  by_cases hn : n ∣ H+1
  · have hq := Nat.succ_div_of_dvd hn
    have hprod := Nat.mul_div_cancel' hn
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn (Nat.succ_pos H)
    have he : 2*n ∣ H+1 ↔ 2 ∣ (H+1)/n := by
      conv_lhs => rw [← hprod,Nat.mul_comm 2 n]
      exact Nat.mul_dvd_mul_iff_left hnpos
    simp only [if_pos hn,he,hq]
    by_cases h : H/n%2=1
    · simp [h,show (H/n+1)%2 ≠ 1 by omega, show 2∣H/n+1 by omega] <;> ring
    · simp [h,show (H/n+1)%2=1 by omega,show ¬2∣H/n+1 by omega]
  · have h2 : ¬ 2*n ∣ H+1 := fun h => hn ((dvd_mul_left n 2).trans h)
    simp [Nat.succ_div_of_not_dvd hn,hn,h2]

/-- The complete signed discrete derivative on any fixed denominator set. -/
theorem oddPrimeJump_divisors (S : Finset ℕ) {u : ℕ} (hu : 0 < u) :
    oddPrimeJump S u = divisorPrimeExcess S u -
      2*∑ n ∈ S, if 2*n ∣ u then ordinaryPrimeExcessCoeff n else 0 := by
  obtain ⟨H,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu.ne'
  simp only [oddPrimeJump,oddQuotientPrimeExcess,divisorPrimeExcess,Nat.succ_sub_one,
    mul_sum,← sum_sub_distrib]
  exact sum_congr rfl fun n _ => digit_jump n H _

/-- At an odd endpoint the quotient jump is the ordinary divisor reading. -/
theorem oddPrimeJump_odd (S : Finset ℕ) {u : ℕ} (hu : Odd u) :
    oddPrimeJump S u = divisorPrimeExcess S u := by
  have hpos : 0 < u := by obtain ⟨j,h⟩ := hu; omega
  rw [oddPrimeJump_divisors S hpos]
  have hn (n : ℕ) : ¬2*n ∣ u := fun h => (Nat.not_even_iff_odd.mpr hu)
    (even_iff_two_dvd.mpr ((dvd_mul_right 2 n).trans h))
  simp [hn]

/-- Doubling introduces one lower divisor fibre with coefficient minus two. -/
theorem oddPrimeJump_double (S : Finset ℕ) {u : ℕ} (hu : 0 < u) :
    oddPrimeJump S (2*u) = divisorPrimeExcess S (2*u) - 2*divisorPrimeExcess S u := by
  rw [oddPrimeJump_divisors S (by omega)]
  simp only [divisorPrimeExcess,Nat.mul_dvd_mul_iff_left (by decide : 0<2)]

/-- Dyadic inversion at any odd base recovers the full divisor excess from
jumps, including their signs, at the ancestors of that numerator. -/
theorem divisorPrimeExcess_dyadic (S : Finset ℕ) {u : ℕ} (hu : Odd u) (v : ℕ) :
    divisorPrimeExcess S (2^v*u) =
      ∑ j ∈ range (v+1), (2:ℝ)^(v-j)*oddPrimeJump S (2^j*u) := by
  have hpos : 0 < u := by obtain ⟨j,h⟩ := hu; omega
  induction v with
  | zero => simp [oddPrimeJump_odd S hu]
  | succ v ih =>
    have h := oddPrimeJump_double S (show 0<2^v*u by positivity)
    rw [show 2*(2^v*u)=2^(v+1)*u by ring] at h
    rw [Finset.sum_range_succ,Nat.sub_self,pow_zero,one_mul]
    have hs : ∑ j ∈ range (v+1), (2:ℝ)^(v+1-j)*oddPrimeJump S (2^j*u) =
        2*∑ j ∈ range (v+1), (2:ℝ)^(v-j)*oddPrimeJump S (2^j*u) := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [show v+1-j=v-j+1 by omega,pow_succ]
      ring
    rw [hs,← ih]
    linarith only [h]

private theorem full_divisor_excess {u X : ℕ} (hu : 0 < u) (hX : u ≤ X) :
    divisorPrimeExcess (Ioc 0 X) u = (∑ p ∈ u.primeFactors, Real.log p) - u.divisors.card := by
  have he : (Ioc 0 X).filter (· ∣ u) = u.divisors := by
    ext n
    simp only [mem_filter,mem_Ioc,Nat.mem_divisors,ne_eq,hu.ne',not_false_eq_true,and_true]
    exact ⟨fun h => h.2,fun h => ⟨⟨Nat.pos_of_dvd_of_pos h hu,(Nat.le_of_dvd hu h).trans hX⟩,h⟩⟩
  have hp : u.divisors.filter Nat.Prime = u.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_divisors,Nat.mem_primeFactors]
    tauto
  rw [divisorPrimeExcess,← sum_filter,he]
  simp only [ordinaryPrimeExcessCoeff,sum_sub_distrib,← sum_filter,hp,sum_const,nsmul_eq_mul,mul_one]

/-- At twice an odd integer all divisor counts cancel. The jump records the
logarithm of two minus the sum of logarithms of the odd prime divisors. -/
theorem oddPrimeJump_twice_odd_full {u X : ℕ} (hu : Odd u) (hX : 2*u ≤ X) :
    oddPrimeJump (Ioc 0 X) (2*u) = Real.log 2 - ∑ p ∈ u.primeFactors, Real.log p := by
  have hpos : 0 < u := by obtain ⟨j,h⟩ := hu; omega
  have hcop := Nat.coprime_two_left.mpr hu
  have hnot : 2 ∉ u.primeFactors := fun h => hu.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors h)
  rw [oddPrimeJump_double _ hpos, full_divisor_excess (by omega) hX,
    full_divisor_excess hpos (by omega),hcop.card_divisors_mul,hcop.primeFactors_mul,
    Nat.prime_two.primeFactors, singleton_union, sum_insert hnot]
  have htwo : (2:ℕ).divisors.card = 2 := by rw [Nat.prime_two.divisors]; simp
  rw [htwo,Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem full_even_divisor_excess {u X : ℕ} (hu : Odd u) (r : ℕ)
    (hX : 2^(r+1)*u≤X) :
    divisorPrimeExcess (Ioc 0 X) (2^(r+1)*u) =
      Real.log 2 + (∑ p ∈ u.primeFactors, Real.log p) -
        ((r:ℝ)+2)*u.divisors.card := by
  have hu₀ : 0<u := by obtain ⟨j,hj⟩ := hu; omega
  have hc := (Nat.coprime_two_left.mpr hu).pow_left (r+1)
  have hnot : 2∉u.primeFactors := fun h => hu.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors h)
  rw [full_divisor_excess (by positivity) hX,hc.card_divisors_mul,hc.primeFactors_mul,
    Nat.primeFactors_pow 2 (Nat.succ_ne_zero r),Nat.prime_two.primeFactors,singleton_union,sum_insert hnot,
    Nat.divisors_prime_pow Nat.prime_two,card_map,card_range,Nat.cast_mul]
  push_cast
  ring

/-- From dyadic exponent two onward the jump is affine in that exponent.
Its slope is the number of divisors of the odd core. -/
theorem oddPrimeJump_higher_full {u X : ℕ} (hu : Odd u) (r : ℕ) (hX : 2^(r+2)*u≤X) :
    oddPrimeJump (Ioc 0 X) (2^(r+2)*u) =
      ((r:ℝ)+1)*u.divisors.card - Real.log 2 - ∑ p ∈ u.primeFactors, Real.log p := by
  have hu₀ : 0<u := by obtain ⟨j,hj⟩ := hu; omega
  have hscale : 2^(r+2)*u = 2*(2^(r+1)*u) := by rw [pow_succ (2:ℕ) (r+1)]; ring
  have hX' : 2^(r+1)*u≤X := by rw [hscale] at hX; omega
  rw [hscale,oddPrimeJump_double _ (by positivity),← hscale,
    full_even_divisor_excess hu (r+1) hX,full_even_divisor_excess hu r hX',Nat.cast_succ]
  ring

/-- Two successive high dyadic jumps read the divisor count of the odd
core. The cutoff needs only to contain the later numerator. -/
theorem dyadic_jump_difference_reads_divisor_count {u X : ℕ} (hu : Odd u) (r : ℕ)
    (hX : 2^(r+3)*u≤X) :
    oddPrimeJump (Ioc 0 X) (2^(r+3)*u) - oddPrimeJump (Ioc 0 X) (2^(r+2)*u) = u.divisors.card := by
  have hs : 2^(r+3)*u=2*(2^(r+2)*u) := by rw [pow_succ (2:ℕ) (r+2)]; ring
  have hX' : 2^(r+2)*u≤X := by rw [hs] at hX; omega
  rw [oddPrimeJump_higher_full hu (r+1) hX,oddPrimeJump_higher_full hu r hX',Nat.cast_succ]
  ring

/-- A signed stencil of four numerator jumps has constant value log 2
on every odd core. The radical and divisor count both cancel. -/
theorem four_dyadic_jumps_constant {u X : ℕ} (hu : Odd u) (hX : 8*u≤X) :
    oddPrimeJump (Ioc 0 X) u + oddPrimeJump (Ioc 0 X) (2*u) +
      (oddPrimeJump (Ioc 0 X) (8*u) - oddPrimeJump (Ioc 0 X) (4*u)) = Real.log 2 := by
  have hu₀ : 0<u := by obtain ⟨j,hj⟩ := hu; omega
  have hd := dyadic_jump_difference_reads_divisor_count hu 0 hX
  norm_num at hd
  rw [hd,oddPrimeJump_twice_odd_full hu (by omega),
    oddPrimeJump_odd _ hu,full_divisor_excess hu₀ (by omega)]
  ring


end
end GaloisForLFunctions.ExclusionOfTheCriticalState
