import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreHomothety

/-!
# Exact clipped homothety of the divisor source

The partial final dilation block is retained exactly. In the physical square-root
clock it gives a convex interpolation of the two adjacent smaller-cutoff channels.
-/

noncomputable section
open Finset
namespace RHTower

/-- Extend the unsigned channel to its full time prefix, including its zero initial terms. -/
theorem divisorUnsignedDilationChannel_eq_range (M d : ℕ) :
    divisorUnsignedDilationChannel M d =
      ∑ k ∈ range M,(Real.sqrt (k+1 : ℕ)-Real.sqrt k)*primeFreeDivisorDefect (k/d) := by
  have hD0 : primeFreeDivisorDefect 0=0 := by simp [primeFreeDivisorDefect]
  by_cases hd : d=0
  · simp [divisorUnsignedDilationChannel,hd,hD0]
  by_cases hM : M=0
  · simp [divisorUnsignedDilationChannel,hM,Icc_eq_empty_of_lt (by omega : 0<d)]
  by_cases hdM : d ≤ M
  · unfold divisorUnsignedDilationChannel
    rw [← Ico_add_one_right_eq_Icc,show M-1+1=M by omega,sum_Ico_eq_sub _ hdM]
    have hz : (∑ k ∈ range d,(Real.sqrt (k+1 : ℕ)-Real.sqrt k)*primeFreeDivisorDefect (k/d))=0 := by
      apply sum_eq_zero
      intro k hk
      rw [Nat.div_eq_of_lt (mem_range.mp hk),hD0,mul_zero]
    rw [hz,sub_zero]
  · unfold divisorUnsignedDilationChannel
    rw [Icc_eq_empty_of_lt (by omega : M-1<d),sum_empty]
    symm
    apply sum_eq_zero
    intro k hk
    rw [Nat.div_eq_of_lt (by have := mem_range.mp hk; omega : k<d),hD0,mul_zero]

/-- Exact homothety with the entire clipped last block, including zero and terminal channels. -/
theorem divisorUnsignedDilationChannel_mul_add (r N t d : ℕ) (hr : 0<r) (ht : t ≤ r) :
    divisorUnsignedDilationChannel (r*N+t) (r*d) =
      Real.sqrt r*divisorUnsignedDilationChannel N d+
        (Real.sqrt (r*N+t : ℕ)-Real.sqrt (r*N : ℕ))*primeFreeDivisorDefect (N/d) := by
  rw [divisorUnsignedDilationChannel_eq_range,sum_range_add,
    ← divisorUnsignedDilationChannel_eq_range,divisorUnsignedDilationChannel_mul]
  congr 1
  have hdiv (i : ℕ) (hi : i ∈ range t) : (r*N+i)/(r*d)=N/d := by
    rw [← Nat.div_div_eq_div_mul,Nat.mul_add_div hr,
      Nat.div_eq_of_lt (lt_of_lt_of_le (mem_range.mp hi) ht),Nat.add_zero]
  calc
    _ = ∑ i ∈ range t,(Real.sqrt (r*N+i+1 : ℕ)-Real.sqrt (r*N+i : ℕ))*primeFreeDivisorDefect (N/d) := by
      apply sum_congr rfl
      intro i hi
      rw [hdiv i hi]
    _ = _ := by
      rw [← sum_mul]
      have htel := sum_range_sub (fun i : ℕ => Real.sqrt (r*N+i : ℕ)) t
      simpa only [Nat.add_assoc,Nat.add_zero] using congrArg (fun z => z*primeFreeDivisorDefect (N/d)) htel

/-- Unsigned successor law holds at every source index, including newly born and zero channels. -/
theorem divisorUnsignedDilationChannel_succ (N d : ℕ) :
    divisorUnsignedDilationChannel (N+1) d = divisorUnsignedDilationChannel N d+
      (Real.sqrt (N+1 : ℕ)-Real.sqrt N)*primeFreeDivisorDefect (N/d) := by
  simpa using divisorUnsignedDilationChannel_mul_add 1 N 1 d (by omega) (by omega)

/-- Fraction of the final prime block in the literal square-root clock. -/
def divisorPrimeClipWeight (M p : ℕ) : ℝ :=
  (Real.sqrt M-Real.sqrt (p*(M/p) : ℕ))/
    (Real.sqrt (p*(M/p+1) : ℕ)-Real.sqrt (p*(M/p) : ℕ))

private theorem clip_den_pos (M p : ℕ) (hp : 0<p) :
    0<Real.sqrt (p*(M/p+1) : ℕ)-Real.sqrt (p*(M/p) : ℕ) := by
  apply sub_pos.mpr
  apply Real.sqrt_lt_sqrt (Nat.cast_nonneg _)
  exact_mod_cast (show p*(M/p)<p*(M/p+1) by nlinarith)

/-- The literal clipping coefficient is nonnegative. -/
theorem divisorPrimeClipWeight_nonneg (M p : ℕ) (hp : 0<p) :
    0 ≤ divisorPrimeClipWeight M p := by
  apply div_nonneg _ (clip_den_pos M p hp).le
  apply sub_nonneg.mpr
  apply Real.sqrt_le_sqrt
  exact_mod_cast (show p*(M/p) ≤ M by simpa [mul_comm] using Nat.div_mul_le_self M p)

/-- A canonical quotient block is strictly short of its next endpoint. -/
theorem divisorPrimeClipWeight_lt_one (M p : ℕ) (hp : 0<p) :
    divisorPrimeClipWeight M p<1 := by
  rw [divisorPrimeClipWeight,div_lt_one (clip_den_pos M p hp)]
  have hM : M<p*(M/p+1) := by
    have := Nat.mod_lt M hp
    have := Nat.mod_add_div M p
    nlinarith
  have hs : Real.sqrt M<Real.sqrt (p*(M/p+1) : ℕ) :=
    Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (by exact_mod_cast hM)
  linarith

/-- The physical interpolation coefficient exactly reconstructs the clipped square-root mass. -/
theorem divisorPrimeClipWeight_mul_step (M p : ℕ) (hp : 0<p) :
    divisorPrimeClipWeight M p*Real.sqrt p*
      (Real.sqrt (M/p+1 : ℕ)-Real.sqrt (M/p : ℕ)) =
        Real.sqrt M-Real.sqrt (p*(M/p) : ℕ) := by
  have hd : Real.sqrt (p*(M/p+1) : ℕ)-Real.sqrt (p*(M/p) : ℕ) =
      Real.sqrt p*(Real.sqrt (M/p+1 : ℕ)-Real.sqrt (M/p : ℕ)) := by
    push_cast
    simp only [Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) p)]
    ring
  rw [mul_assoc,← hd,divisorPrimeClipWeight]
  exact div_mul_cancel₀ _ (ne_of_gt (clip_den_pos M p hp))

/-- Every dilated channel is an exact convex interpolation of two adjacent smaller channels. -/
theorem divisorUnsignedDilationChannel_prime_interpolation (M p d : ℕ) (hp : 0<p) :
    divisorUnsignedDilationChannel M (p*d) = Real.sqrt p*
      ((1-divisorPrimeClipWeight M p)*divisorUnsignedDilationChannel (M/p) d+
        divisorPrimeClipWeight M p*divisorUnsignedDilationChannel (M/p+1) d) := by
  have he : p*(M/p)+M%p=M := by have := Nat.mod_add_div M p; omega
  have hc := divisorUnsignedDilationChannel_mul_add p (M/p) (M%p) d hp (Nat.mod_lt M hp).le
  rw [he] at hc
  rw [hc,divisorUnsignedDilationChannel_succ]
  have hw := divisorPrimeClipWeight_mul_step M p hp
  nlinarith only [congrArg (fun z => z*primeFreeDivisorDefect ((M/p)/d)) hw]

/-- Coprime prime multiplication retains its sign through the full clipped interpolation. -/
theorem mobiusDivisorDilationChannel_prime_interpolation {p : ℕ} (hp : p.Prime)
    (M d : ℕ) (hpd : ¬p ∣ d) :
    mobiusDivisorDilationChannel M (p*d) = -Real.sqrt p*
      ((1-divisorPrimeClipWeight M p)*mobiusDivisorDilationChannel (M/p) d+
        divisorPrimeClipWeight M p*mobiusDivisorDilationChannel (M/p+1) d) := by
  have hc : p.Coprime d := hp.coprime_iff_not_dvd.mpr hpd
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
    ArithmeticFunction.moebius_apply_prime hp,divisorUnsignedDilationChannel_prime_interpolation M p d hp.pos,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,mobiusDivisorDilationChannel_eq_moebius_unsigned]
  push_cast
  ring
end RHTower
