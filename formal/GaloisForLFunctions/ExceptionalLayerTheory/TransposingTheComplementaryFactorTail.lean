import GaloisForLFunctions.ExceptionalLayerTheory.AveragingThePrimeErrorAtAComplementaryBoundary
import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# The centered boundary in a transposed complementary tail

Differencing the quotient weight replaces the tail in the complementary
factor by a difference of two centered floor primitives. The lower
boundary is independent of the new factor.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem sum_backward_difference (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ v ∈ Icc (a+1) b, (f v-f (v-1)))=f b-f a := by
  induction b, hab using Nat.le_induction with
  | base => rw [Icc_eq_empty (by omega),sum_empty,sub_self]
  | succ b hab ih =>
    rw [sum_Icc_succ_top (by omega),ih,Nat.add_sub_cancel]
    ring

/-- For a positive quotient the outer jumps recover its weight, including
the contribution at the first integer. -/
theorem outerJump_sum_at_positive (R : ℕ) {t : ℕ} (ht : 1≤t) :
    ∑ j ∈ Icc 1 t, outerJump R j = centeredPrimeWeight R t := by
  let f (j : ℕ) := if j=0 then (0 : ℝ) else centeredPrimeWeight R j
  change (∑ j ∈ Icc 1 t, (f j-f (j-1)))=_
  rw [sum_backward_difference f (Nat.zero_le t)]
  simp [f,Nat.ne_of_gt ht]

/-- Above a positive lower limit the constants in the two inner
primitives cancel. -/
theorem innerJump_sum_between {a b : ℕ} (D : ℕ) (ha : 1≤a) (hab : a≤b) :
    ∑ v ∈ Icc (a+1) b, innerJump D v = factorialBoundary (D+1) b-factorialBoundary (D+1) a := by
  let f (v : ℕ) := if v=0 then (0 : ℝ) else 1-factorialPrefix (D+1) v
  change (∑ v ∈ Icc (a+1) b, (f v-f (v-1)))=_
  rw [sum_backward_difference f hab]
  simp only [f,if_neg (Nat.ne_of_gt ha),if_neg (Nat.ne_of_gt (ha.trans hab)),factorialBoundary]
  ring

/-- Exact hyperbola identity for every positive lower complementary cutoff. -/
theorem complementary_tail_transpose (D R T : ℕ) {a : ℕ} (ha : 1≤a) :
    (∑ v ∈ Ioc a T, innerJump D v*centeredPrimeWeight R (T/v)) =
      (∑ j ∈ Icc 1 (T/(a+1)), outerJump R j*factorialBoundary (D+1) (T/j))-
        factorialBoundary (D+1) a*∑ j ∈ Icc 1 (T/(a+1)), outerJump R j := by
  rw [show Ioc a T=Icc (a+1) T by ext n; simp only [mem_Ioc,mem_Icc]; omega]
  calc _ = ∑ v ∈ Icc (a+1) T, ∑ j ∈ Icc 1 (T/v), outerJump R j*innerJump D v := by
            apply sum_congr rfl; intro v hv
            obtain ⟨hlo,hhi⟩ := mem_Icc.mp hv
            have hq : 1≤T/v := (Nat.le_div_iff_mul_le (by omega : 0<v)).mpr (by simpa only [one_mul] using hhi)
            rw [←sum_mul,outerJump_sum_at_positive R hq,mul_comm]
       _ = ∑ j ∈ Icc 1 (T/(a+1)), ∑ v ∈ Icc (a+1) (T/j), outerJump R j*innerJump D v :=
            sum_hyperbola_tail_swap_real T (a+1) _ (Nat.succ_pos a)
       _ = _ := by
            rw [mul_sum,←sum_sub_distrib]
            apply sum_congr rfl; intro j hj
            obtain ⟨hj₁,hhi⟩ := mem_Icc.mp hj
            have hmul := (Nat.le_div_iff_mul_le (Nat.succ_pos a)).mp hhi
            have hq : a+1≤T/j := (Nat.le_div_iff_mul_le hj₁).mpr (by rwa [Nat.mul_comm] at hmul)
            rw [←mul_sum,innerJump_sum_between D ha (Nat.le_succ a |>.trans hq)]
            ring

#print axioms complementary_tail_transpose
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
