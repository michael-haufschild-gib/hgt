/-
# Bondarenko--Heap Lemma 10: primitive-conductor zero-density aggregation

The zero-density step in Lemma 10 replaces characters modulo `q` by their
primitive inducing characters.  Source equation (38) aggregates the resulting
zero counts over primitive characters of each conductor dividing `q`.  This
module makes that finite aggregation literal and proves its closed domination
by the existing conductor-range zero-box family.  It does not assert the
Chen--Gupta--Li conductor-uniform exponent; that deeper large-values theorem
is developed in the subsequent zero-density module.
-/
import GaloisForLFunctions.RHTower.DirichletLZeroDensityPrimitive

open Complex Metric

noncomputable section

namespace RHTower

/-- Literal primitive-character zero-density count over every conductor
dividing the ambient modulus.  This is the finite source aggregation in
Bondarenko--Heap equation (38). -/
noncomputable def completedLFunctionPrimitiveDivisorZeroDensityBoxCount
    (q : ℕ) (σ H : ℝ) : ℝ :=
  ∑ d ∈ q.divisors, completedLFunctionPrimitiveFamilyZeroDensityBoxCount d σ H

/-- Each exact-modulus primitive nonprincipal zero-box family has a
nonnegative multiplicity-weighted count. -/
theorem completedLFunction_primitiveFamily_zeroDensityBoxCount_nonneg
    (n : ℕ) (σ H : ℝ) : 0 ≤ completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H := by
  classical
  unfold completedLFunctionPrimitiveFamilyZeroDensityBoxCount
  apply Finset.sum_nonneg
  intro χ hχ
  split_ifs with hprim
  · exact completedLFunction_zeroDensityBoxCount_nonneg n χ σ H
  · positivity

/-- The divisor-conductor aggregation is nonnegative. -/
theorem completedLFunction_primitiveDivisor_zeroDensityBoxCount_nonneg
    (q : ℕ) (σ H : ℝ) :
    0 ≤ completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ H := by
  unfold completedLFunctionPrimitiveDivisorZeroDensityBoxCount
  exact Finset.sum_nonneg fun d hd =>
    completedLFunction_primitiveFamily_zeroDensityBoxCount_nonneg d σ H

/-- Every primitive conductor dividing `q` lies in the concrete finite range
through `q`; therefore the exact divisor aggregation is bounded by the
previously certified full primitive conductor range. -/
theorem completedLFunction_primitiveDivisor_zeroDensityBoxCount_le_range
    (q : ℕ) (σ H : ℝ) :
    completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ H ≤
      completedLFunctionPrimitiveRangeZeroDensityBoxCount (q + 1) σ H := by
  rw [completedLFunctionPrimitiveDivisorZeroDensityBoxCount,
    completedLFunctionPrimitiveRangeZeroDensityBoxCount]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hq : q ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hdle : d ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd
    exact Finset.mem_range.mpr (by omega)
  · intro d hd hnot
    exact completedLFunction_primitiveFamily_zeroDensityBoxCount_nonneg d σ H

end RHTower
