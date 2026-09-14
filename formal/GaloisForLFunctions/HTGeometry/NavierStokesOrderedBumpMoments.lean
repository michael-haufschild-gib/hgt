import GaloisForLFunctions.HTGeometry.NavierStokesRealExponentialVandermonde
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Ordered-bump real-power moment maps

This file formalizes the arbitrary-size moment-map invertibility assertion in Lemma A.1 of the
supplied Navier-Stokes paper.  Each nonnegative bump is supported in its own positive interval,
and those intervals are strictly ordered.  The first mean-value theorem for integrals selects one
node from every bump.  A vector in the transpose kernel would therefore give a real-power sum
vanishing at all selected nodes, contradicting generalized exponential Vandermonde rigidity.
-/

noncomputable section

open Finset Function MeasureTheory Set
open scoped Interval

namespace GaloisForLFunctions.HTGeometry.NavierStokesOrderedBumpMoments

/-- Linear combination of positive real powers. -/
noncomputable def realPowerSum {n : ℕ} (c α : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * x ^ (α i)

/-- The actual global moment matrix `Bᵢⱼ = ∫ x^αᵢ βⱼ(x) dx` from Lemma A.1. -/
noncomputable def realPowerMomentMatrix {n : ℕ} (α : Fin n → ℝ)
    (β : Fin n → ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ ∫ x, x ^ (α i) * β j x ∂volume

private theorem support_rpow_mul_subset {p a b : ℝ} {β : ℝ → ℝ}
    (hsupp : support β ⊆ Ioc a b) :
    support (fun x : ℝ ↦ x ^ p * β x) ⊆ Ioc a b := by
  intro x hx
  apply hsupp
  intro hzero
  apply hx
  simp [hzero]

/-- Compact support replaces a global moment integral by its containing interval integral. -/
theorem realPowerMomentMatrix_apply_interval {n : ℕ} (α : Fin n → ℝ)
    (β : Fin n → ℝ → ℝ) (a b : Fin n → ℝ) (i j : Fin n)
    (hsupp : support (β j) ⊆ Ioc (a j) (b j)) :
    realPowerMomentMatrix α β i j =
      ∫ x in a j..b j, x ^ (α i) * β j x := by
  symm
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (support_rpow_mul_subset hsupp)

/-- A continuous nonnegative, nonzero bump has positive mass on an interval containing its
support. -/
theorem bump_intervalIntegral_pos {β : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hcont : Continuous β) (hnonneg : ∀ x, 0 ≤ β x)
    (hne : β ≠ 0) (hsupp : support β ⊆ Ioc a b) :
    0 < ∫ x in a..b, β x := by
  apply intervalIntegral.integral_pos hab hcont.continuousOn
  · intro x hx
    exact hnonneg x
  · have hex : ∃ x, β x ≠ 0 := by
      by_contra h
      apply hne
      funext x
      by_contra hx
      exact h ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hex
    have hxmem := hsupp hx
    refine ⟨x, ⟨hxmem.1.le, hxmem.2⟩, ?_⟩
    exact lt_of_le_of_ne (hnonneg x) hx.symm

/-- **Lemma A.1, arbitrary-size moment-map invertibility.** Distinct ordered real exponents
and nonnegative nonzero bumps supported in strictly ordered positive intervals produce an
invertible global real-power moment matrix. -/
theorem isUnit_realPowerMomentMatrix {n : ℕ} (α a b : Fin n → ℝ)
    (β : Fin n → ℝ → ℝ)
    (hα : StrictMono α)
    (ha : ∀ j, 0 < a j) (hab : ∀ j, a j < b j)
    (hsep : ∀ {i j : Fin n}, i < j → b i < a j)
    (hβcont : ∀ j, Continuous (β j))
    (hβnonneg : ∀ j x, 0 ≤ β j x)
    (hβne : ∀ j, β j ≠ 0)
    (hβsupp : ∀ j, support (β j) ⊆ Ioc (a j) (b j)) :
    IsUnit (realPowerMomentMatrix α β) := by
  rw [← Matrix.isUnit_transpose, ← Matrix.mulVec_injective_iff_isUnit]
  suffices hker : ∀ c : Fin n → ℝ,
      (realPowerMomentMatrix α β).transpose.mulVec c = 0 → c = 0 by
    intro c d hcd
    apply sub_eq_zero.mp
    apply hker (c - d)
    rw [Matrix.mulVec_sub, hcd, sub_self]
  intro c hc
  have hpowCont : ∀ i j : Fin n,
      ContinuousOn (fun x : ℝ ↦ x ^ (α i)) (Icc (a j) (b j)) := by
    intro i j
    exact continuousOn_id.rpow_const fun x hx ↦
      Or.inl ((ha j).trans_le hx.1).ne'
  have hsumCont : ∀ j : Fin n,
      ContinuousOn (realPowerSum c α) (Icc (a j) (b j)) := by
    intro j
    unfold realPowerSum
    exact continuousOn_finsetSum univ fun i _ ↦
      continuousOn_const.mul (hpowCont i j)
  have hnode : ∀ j : Fin n, ∃ y ∈ Icc (a j) (b j), realPowerSum c α y = 0 := by
    intro j
    have hβint : IntervalIntegrable (β j) volume (a j) (b j) :=
      (hβcont j).continuousOn.intervalIntegrable_of_Icc (hab j).le
    obtain ⟨y, hy, hmean⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
      (by simpa [uIcc_of_le (hab j).le] using hsumCont j)
      hβint (fun x _ ↦ hβnonneg j x)
    refine ⟨y, by simpa [uIcc_of_le (hab j).le] using hy, ?_⟩
    have htermInt : ∀ i : Fin n,
        IntervalIntegrable (fun x : ℝ ↦ x ^ (α i) * β j x)
          volume (a j) (b j) := by
      intro i
      exact ((hpowCont i j).mul (hβcont j).continuousOn).intervalIntegrable_of_Icc
        (hab j).le
    have hintegral :
        (∫ x in a j..b j, realPowerSum c α x * β j x) =
          ∑ i, c i * realPowerMomentMatrix α β i j := by
      calc
        _ = ∫ x in a j..b j, ∑ i, c i * (x ^ (α i) * β j x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          simp [realPowerSum, Finset.sum_mul, mul_assoc]
        _ = ∑ i, ∫ x in a j..b j, c i * (x ^ (α i) * β j x) := by
          apply intervalIntegral.integral_finsetSum
          intro i hi
          exact (htermInt i).const_mul _
        _ = ∑ i, c i * (∫ x in a j..b j, x ^ (α i) * β j x) := by
          apply sum_congr rfl
          intro i hi
          rw [intervalIntegral.integral_const_mul]
        _ = ∑ i, c i * realPowerMomentMatrix α β i j := by
          apply sum_congr rfl
          intro i hi
          rw [realPowerMomentMatrix_apply_interval α β a b i j (hβsupp j)]
    have hintegralZero :
        (∫ x in a j..b j, realPowerSum c α x * β j x) = 0 := by
      rw [hintegral]
      have hcj := congrFun hc j
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hcj
    rw [hintegralZero] at hmean
    exact (mul_eq_zero.mp hmean.symm).resolve_right
      (bump_intervalIntegral_pos (hab j) (hβcont j) (hβnonneg j)
        (hβne j) (hβsupp j)).ne'
  choose y hy hyzero using hnode
  have hypos : ∀ j, 0 < y j := fun j ↦ (ha j).trans_le (hy j).1
  have hystrict : StrictMono y := by
    intro i j hij
    exact (hy i).2.trans_lt ((hsep hij).trans_le (hy j).1)
  have hlogStrict : StrictMono (fun j ↦ Real.log (y j)) := by
    intro i j hij
    exact Real.strictMonoOn_log (mem_Ioi.mpr (hypos i)) (mem_Ioi.mpr (hypos j))
      (hystrict hij)
  have hVunit :=
    NavierStokesRealExponentialVandermonde.isUnit_realExponentialVandermonde
      α (fun j ↦ Real.log (y j)) hα hlogStrict
  apply Matrix.mulVec_injective_of_isUnit hVunit
  funext j
  have hz := hyzero j
  rw [realPowerSum] at hz
  simpa [NavierStokesRealExponentialVandermonde.realExponentialVandermonde,
    Matrix.mulVec, dotProduct, Real.rpow_def_of_pos (hypos j), mul_comm] using hz

end GaloisForLFunctions.HTGeometry.NavierStokesOrderedBumpMoments
