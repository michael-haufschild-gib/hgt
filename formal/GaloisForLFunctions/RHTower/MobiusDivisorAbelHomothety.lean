import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# Exact integer homothety of literal Möbius–divisor channels

The unsigned half-order response scales by the square root of a common integer
dilation. The signed response retains Möbius multiplicativity and the exact
shared-prime mask. Zero indices, empty channels and terminal blocks are included.
-/

noncomputable section
open Finset
namespace RHTower

/-- The literal unsigned half-order floor-dilation channel. -/
def divisorUnsignedDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Icc d (M-1), (Real.sqrt (k+1 : ℕ)-Real.sqrt k)*primeFreeDivisorDefect (k/d)

private theorem unsigned_prefix (M d : ℕ) :
    divisorUnsignedDilationChannel M d =
      ∑ k ∈ range M, (Real.sqrt (k+1 : ℕ)-Real.sqrt k)*primeFreeDivisorDefect (k/d) := by
  have hD0 : primeFreeDivisorDefect 0 = 0 := by simp [primeFreeDivisorDefect]
  by_cases hd : d = 0
  · simp [divisorUnsignedDilationChannel,hd,hD0]
  by_cases hM : M = 0
  · simp [divisorUnsignedDilationChannel,hM,Icc_eq_empty_of_lt (by omega : 0 < d)]
  by_cases hdM : d ≤ M
  · unfold divisorUnsignedDilationChannel
    rw [← Ico_add_one_right_eq_Icc,show M-1+1=M by omega,sum_Ico_eq_sub _ hdM]
    have hz : (∑ k ∈ range d, (Real.sqrt (k+1 : ℕ)-Real.sqrt k)*primeFreeDivisorDefect (k/d)) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [Nat.div_eq_of_lt (mem_range.mp hk),hD0,mul_zero]
    rw [hz,sub_zero]
  · unfold divisorUnsignedDilationChannel
    rw [Icc_eq_empty_of_lt (by omega : M-1 < d),sum_empty]
    symm
    apply sum_eq_zero
    intro k hk
    rw [Nat.div_eq_of_lt (by have := mem_range.mp hk; omega : k < d),hD0,mul_zero]

private theorem sum_range_integer_blocks (r M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ range (r*M), f k) = ∑ q ∈ range M, ∑ i ∈ range r, f (r*q+i) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ,sum_range_add,ih,Finset.sum_range_succ]

/-- Exact unsigned homothety, including zero cutoffs and zero dilation indices. -/
theorem divisorUnsignedDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedDilationChannel (r*M) (r*d) = Real.sqrt r*divisorUnsignedDilationChannel M d := by
  rw [unsigned_prefix,unsigned_prefix]
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := by omega
  rw [sum_range_integer_blocks]
  have hblock (q : ℕ) :
      (∑ i ∈ range r, (Real.sqrt (r*q+i+1 : ℕ)-Real.sqrt (r*q+i : ℕ))*
        primeFreeDivisorDefect ((r*q+i)/(r*d))) =
      Real.sqrt r*(Real.sqrt (q+1 : ℕ)-Real.sqrt q)*primeFreeDivisorDefect (q/d) := by
    have hdiv (i : ℕ) (hi : i ∈ range r) : (r*q+i)/(r*d) = q/d := by
      rw [← Nat.div_div_eq_div_mul,Nat.mul_add_div hrpos,
        Nat.div_eq_of_lt (mem_range.mp hi),Nat.add_zero]
    have htel : (∑ i ∈ range r, (Real.sqrt (r*q+i+1 : ℕ)-Real.sqrt (r*q+i : ℕ))) =
        Real.sqrt (r*q+r : ℕ)-Real.sqrt (r*q : ℕ) := by
      simpa only [Nat.add_assoc,Nat.add_zero] using
        sum_range_sub (fun i : ℕ => Real.sqrt (r*q+i : ℕ)) r
    calc
      _ = ∑ i ∈ range r, (Real.sqrt (r*q+i+1 : ℕ)-Real.sqrt (r*q+i : ℕ))*
          primeFreeDivisorDefect (q/d) := by
        apply sum_congr rfl
        intro i hi
        rw [hdiv i hi]
      _ = (∑ i ∈ range r, (Real.sqrt (r*q+i+1 : ℕ)-Real.sqrt (r*q+i : ℕ)))*
          primeFreeDivisorDefect (q/d) := by rw [sum_mul]
      _ = (Real.sqrt (r*q+r : ℕ)-Real.sqrt (r*q : ℕ))*primeFreeDivisorDefect (q/d) := by rw [htel]
      _ = _ := by
        rw [show r*q+r=r*(q+1) by ring]
        push_cast
        simp only [Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) r)]
        ring
  simp_rw [hblock]
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  ring

/-- The Möbius coefficient remains outside the exact unsigned source response. -/
theorem mobiusDivisorDilationChannel_eq_moebius_unsigned (M d : ℕ) :
    mobiusDivisorDilationChannel M d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*divisorUnsignedDilationChannel M d := rfl

/-- Exact signed homothety on disjoint prime supports. -/
theorem mobiusDivisorDilationChannel_mul_coprime {r M d : ℕ}
    (hc : r.Coprime d) :
    mobiusDivisorDilationChannel (r*M) (r*d) =
      Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ)*mobiusDivisorDilationChannel M d := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,divisorUnsignedDilationChannel_mul,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
  push_cast
  ring

/-- Shared prime factors annihilate the signed dilation; no arithmetic support is discarded. -/
theorem mobiusDivisorDilationChannel_mul_masked (r M d : ℕ) :
    mobiusDivisorDilationChannel (r*M) (r*d) =
      Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ)*
        (if r.Coprime d then mobiusDivisorDilationChannel M d else 0) := by
  by_cases hc : r.Coprime d
  · rw [if_pos hc]
    exact mobiusDivisorDilationChannel_mul_coprime hc
  · have hm : ArithmeticFunction.moebius (r*d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun hsf => hc (Nat.coprime_of_squarefree_mul hsf))
    rw [if_neg hc,mul_zero,mobiusDivisorDilationChannel_eq_moebius_unsigned,hm,Int.cast_zero,zero_mul]

end RHTower
