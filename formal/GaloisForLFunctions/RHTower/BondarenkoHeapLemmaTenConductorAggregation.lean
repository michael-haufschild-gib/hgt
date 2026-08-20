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
  ∑ d ∈ q.divisors, completedLFunctionPrimitiveFamilyZeroDensityBoxCount (d - 1) σ H

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
    completedLFunction_primitiveFamily_zeroDensityBoxCount_nonneg (d - 1) σ H

/-- Every primitive conductor dividing `q` lies in the concrete finite range
through `q`; therefore the exact divisor aggregation is bounded by the
previously certified full primitive conductor range. -/
theorem completedLFunction_primitiveDivisor_zeroDensityBoxCount_le_range
    (q : ℕ) (σ H : ℝ) :
    completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ H ≤
      completedLFunctionPrimitiveRangeZeroDensityBoxCount q σ H := by
  rw [completedLFunctionPrimitiveDivisorZeroDensityBoxCount,
    completedLFunctionPrimitiveRangeZeroDensityBoxCount]
  calc
    (∑ d ∈ q.divisors,
      completedLFunctionPrimitiveFamilyZeroDensityBoxCount (d - 1) σ H) =
        ∑ n ∈ q.divisors.image (fun d => d - 1),
          completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      have haq := Nat.mem_divisors.mp ha
      have hbq := Nat.mem_divisors.mp hb
      have ha0 : a ≠ 0 := by
        intro hzero
        have hdiv : 0 ∣ q := by simpa [hzero] using haq.1
        rcases hdiv with ⟨c, hc⟩
        exact haq.2 (by simpa using hc)
      have hb0 : b ≠ 0 := by
        intro hzero
        have hdiv : 0 ∣ q := by simpa [hzero] using hbq.1
        rcases hdiv with ⟨c, hc⟩
        exact hbq.2 (by simpa using hc)
      have haone : 1 ≤ a := by omega
      have hbone : 1 ≤ b := by omega
      change a - 1 = b - 1 at hab
      calc
        a = (a - 1) + 1 := (Nat.sub_add_cancel haone).symm
        _ = (b - 1) + 1 := by rw [hab]
        _ = b := Nat.sub_add_cancel hbone
    _ ≤ ∑ n ∈ Finset.range q,
        completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rcases Finset.mem_image.mp hn with ⟨d, hd, rfl⟩
        have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
        have hq : q ≠ 0 := (Nat.mem_divisors.mp hd).2
        have hdle : d ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd
        exact Finset.mem_range.mpr (by omega)
      · intro n hn hnot
        exact completedLFunction_primitiveFamily_zeroDensityBoxCount_nonneg n σ H

/-- Closed height envelope for the exact primitive-conductor aggregation in source equation (38).
Its constant is constructed at the fixed ambient conductor `q`; it deliberately does not assert
the conductor-uniform Chen--Gupta--Li exponent. -/
theorem completedLFunction_primitiveDivisor_zeroDensityBoxCount_growth
    (q : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ σ H : ℝ,
      completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ H ≤
        C * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
  obtain ⟨C, hC, hbound⟩ :=
    completedLFunction_primitiveRange_zeroDensityBoxCount_growth q
  exact ⟨C, hC, fun σ H ↦
    (completedLFunction_primitiveDivisor_zeroDensityBoxCount_le_range q σ H).trans
      (hbound σ H)⟩

end RHTower
