import GaloisForLFunctions.BiScaleUncertainty.OriginAllocationUniquenessAndCoupledSphereGain

/-!
# Exact allocation equality, including zero totals

Equality in the support bound requires both a zero determinant and a nonnegative
dot product. For finite sums, a zero total vector is a separate boundary case:
then every individual vector must vanish. All real signs and empty sets are included.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.ClassicalBoundaries
set_option autoImplicit false

/-- Full equality criterion for two real vectors, with no positivity or nonzero assumptions. -/
theorem pair_support_eq_iff (W A a q : ℝ) :
    W*a+A*q = Real.sqrt (W^2+A^2)*Real.sqrt (a^2+q^2) ↔
      A*a=W*q ∧ 0 ≤ W*a+A*q := by
  have hleft := Real.sq_sqrt (show 0 ≤ W^2+A^2 by positivity)
  have hright := Real.sq_sqrt (show 0 ≤ a^2+q^2 by positivity)
  have hs : (Real.sqrt (W^2+A^2)*Real.sqrt (a^2+q^2))^2 =
      (W^2+A^2)*(a^2+q^2) := by rw [mul_pow, hleft, hright]
  have hnon : 0 ≤ Real.sqrt (W^2+A^2)*Real.sqrt (a^2+q^2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hlag := origin_pair_lagrange_defect W A a q
  constructor
  · intro heq
    refine ⟨?_, by rw [heq]; exact hnon⟩
    have hz : (A*a-W*q)^2 = 0 := by rw [heq] at hlag; linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro ⟨hprop, hdot⟩
    have hz : A*a-W*q = 0 := sub_eq_zero.mpr hprop
    rw [hz] at hlag
    nlinarith

/-- Exact finite allocation equality on every stratum; zero total mass requires all vectors zero. -/
theorem allocation_eq_iff {ι : Type*} (s : Finset ι) (a q : ι → ℝ) :
    (∑ i ∈ s, Real.sqrt (a i^2+q i^2)) =
      Real.sqrt ((∑ i ∈ s, a i)^2+(∑ i ∈ s, q i)^2) ↔
    if (∑ i ∈ s, a i) = 0 ∧ (∑ i ∈ s, q i) = 0 then
      ∀ i ∈ s, a i = 0 ∧ q i = 0
    else
      ∀ i ∈ s, (∑ j ∈ s, q j)*a i=(∑ j ∈ s, a j)*q i ∧
        0 ≤ (∑ j ∈ s, a j)*a i+(∑ j ∈ s, q j)*q i := by
  set W := ∑ i ∈ s, a i
  set A := ∑ i ∈ s, q i
  by_cases hz : W = 0 ∧ A = 0
  · rw [if_pos hz, hz.1, hz.2]
    norm_num only [zero_pow, zero_add, Real.sqrt_zero]
    constructor
    · intro hc i hi
      have he := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ s) => Real.sqrt_nonneg (a j^2+q j^2))).mp hc i hi
      have hs := Real.sq_sqrt (show 0 ≤ a i^2+q i^2 by positivity)
      rw [he] at hs
      constructor <;> nlinarith [sq_nonneg (a i), sq_nonneg (q i)]
    · intro hall
      apply Finset.sum_eq_zero
      intro i hi
      rw [(hall i hi).1, (hall i hi).2]
      norm_num
  · rw [if_neg hz]
    set S := Real.sqrt (W^2+A^2)
    have hS : 0 < S := by
      apply Real.sqrt_pos.mpr
      by_contra h
      have hn : W^2+A^2 ≤ 0 := le_of_not_gt h
      apply hz
      constructor <;> nlinarith [sq_nonneg W, sq_nonneg A]
    have hSsq : S^2=W^2+A^2 := Real.sq_sqrt (by positivity)
    have hn (i : ι) (_ : i ∈ s) :
        0 ≤ S*Real.sqrt (a i^2+q i^2)-(W*a i+A*q i) :=
      sub_nonneg.mpr (origin_pair_support W A (a i) (q i))
    have hid : (∑ i ∈ s, (S*Real.sqrt (a i^2+q i^2)-(W*a i+A*q i))) =
        S*((∑ i ∈ s, Real.sqrt (a i^2+q i^2))-S) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      change S*(∑ i ∈ s, Real.sqrt (a i^2+q i^2))-(W*W+A*A) = _
      nlinarith only [hSsq]
    constructor
    · intro heq i hi
      have hsum : (∑ i ∈ s, (S*Real.sqrt (a i^2+q i^2)-(W*a i+A*q i))) = 0 := by
        rw [hid, heq, sub_self, mul_zero]
      have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum i hi
      exact (pair_support_eq_iff W A (a i) (q i)).mp (sub_eq_zero.mp he).symm
    · intro hall
      have hsum : (∑ i ∈ s, (S*Real.sqrt (a i^2+q i^2)-(W*a i+A*q i))) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have he := (pair_support_eq_iff W A (a i) (q i)).mpr (hall i hi)
        exact sub_eq_zero.mpr he.symm
      rw [hid] at hsum
      exact sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hS.ne')

end GaloisForLFunctions.BiScaleUncertainty.ClassicalBoundaries
