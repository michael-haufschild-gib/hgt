import GaloisForLFunctions.ExceptionalLayerTheory.PrimePowerMassInTheBalancedProduct

/-!
# The inner coefficient on multiples of a large prime

All divisors in the corrected floor weight are coprime to a prime beyond
its support. Dilation by that prime preserves every increment past the
first and changes the full positive prefix by exactly one.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def floorJump (n d : ℕ) : ℝ :=
  ((n/d : ℕ) : ℝ)-(((n-1)/d : ℕ) : ℝ)

private theorem floorJump_eq {n : ℕ} (hn : 1 ≤ n) (d : ℕ) :
    floorJump n d = if d ∣ n then 1 else 0 := by
  have he := Nat.succ_div (a := n-1) (b := d)
  rw [Nat.sub_add_cancel hn] at he
  by_cases hd : d ∣ n
  · rw [if_pos hd] at he ⊢
    simp only [floorJump,he,Nat.cast_add,Nat.cast_one,add_sub_cancel_left]
  · rw [if_neg hd,Nat.add_zero] at he
    rw [if_neg hd,floorJump,he,sub_self]

private theorem innerJump_eq_neg_increment {t : ℕ} (ht : 2 ≤ t) (D : ℕ) :
    innerJump D t = -(stencil (D+1) (floorJump t)) := by
  change (if t=0 then 0 else 1-factorialPrefix (D+1) t)-
    (if t-1=0 then 0 else 1-factorialPrefix (D+1) (t-1)) = _
  rw [if_neg (by omega),if_neg (by omega)]
  simp only [floorJump,stencil_sub,factorialPrefix]
  ring

/-- Multiplying by a prime beyond the divisor support preserves the inner
coefficient except at the unit argument, where the difference is minus one. -/
theorem innerJump_prime_multiple {D p t : ℕ} (hD : 1 ≤ D) (hp : p.Prime)
    (hlarge : 2*(D+1) < p) (ht : 1 ≤ t) :
    innerJump D (p*t) = innerJump D t-(if t=1 then 1 else 0) := by
  by_cases ht₁ : t=1
  · subst t
    rw [Nat.mul_one,innerJump_at_prime hD hp hlarge,innerJump_small hD,if_pos rfl]
    ring
  have hpt : 2 ≤ p*t := (show 2 ≤ t by omega).trans (Nat.le_mul_of_pos_left t hp.pos)
  have hsame (d : ℕ) (hd : d ∈ Icc 1 (2*(D+1))) : floorJump (p*t) d = floorJump t d := by
    obtain ⟨hd₁,hd₂⟩ := mem_Icc.mp hd
    have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hd₁ (hd₂.trans_lt hlarge))).symm
    rw [floorJump_eq (by omega : 1 ≤ p*t),floorJump_eq ht,hcop.dvd_mul_left]
  have he := abs_stencil_le (Nat.succ_pos D) (M := 0) (fun d => floorJump (p*t) d-floorJump t d)
    (fun d hd => by rw [hsame d hd,sub_self,abs_zero])
  rw [mul_zero,abs_nonpos_iff,stencil_sub,sub_eq_zero] at he
  rw [innerJump_eq_neg_increment hpt,innerJump_eq_neg_increment (by omega : 2 ≤ t),he,if_neg ht₁,sub_zero]

/-- The prefix on large prime multiples differs from the unrestricted
prefix by exactly minus one at every positive endpoint. -/
theorem sum_innerJump_prime_multiple {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime)
    (hlarge : 2*(D+1) < p) (T : ℕ) :
    (∑ t ∈ Icc 1 T, innerJump D (p*t)) =
      (∑ t ∈ Icc 1 T, innerJump D t)-(if T=0 then 0 else 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_Icc_succ_top (by omega),sum_Icc_succ_top (by omega),ih,
      innerJump_prime_multiple hD hp hlarge (Nat.succ_pos T)]
    rcases T with _ | T <;> simp <;> ring

/-- The bound for shared-prime prefixes is independent of both the prime
and the summation length. -/
theorem innerJump_prime_multiple_prefix_bound {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime)
    (hlarge : 2*(D+1) < p) (T : ℕ) :
    |∑ t ∈ Icc 1 T, innerJump D (p*t)| ≤ 2+mass (D+1) := by
  rw [sum_innerJump_prime_multiple hD hp hlarge]
  apply (abs_sub _ _).trans
  have h := innerJump_prefix_bound D T
  split <;> simp only [abs_zero,abs_one] <;> linarith only [h]

/-- On every interval above one, imposing the large prime multiplier
leaves the signed sum exactly unchanged. -/
theorem innerJump_prime_multiple_interval {D p L U : ℕ} (hD : 1 ≤ D) (hp : p.Prime)
    (hlarge : 2*(D+1) < p) (hL : 1 ≤ L) :
    (∑ t ∈ Ioc L U, innerJump D (p*t)) = ∑ t ∈ Ioc L U, innerJump D t := by
  apply sum_congr rfl
  intro t ht
  have hlt := (mem_Ioc.mp ht).1
  rw [innerJump_prime_multiple hD hp hlarge (by omega),if_neg (by omega),sub_zero]

#print axioms innerJump_prime_multiple_prefix_bound
#print axioms innerJump_prime_multiple_interval

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
