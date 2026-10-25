import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Power-tail coefficients across the critical payment boundary

Successive differences of a decreasing power tail have absolute sum two
and zero total evaluation. Their partial sums recover the negative tail
exactly, so the classical power-series criterion gives the precise
square-energy threshold for every positive tail exponent.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A shifted inverse-power tail. -/
def criticalPowerTail (α : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-α)

/-- The coefficient differences whose inclusive partial sums are the negative power tail. -/
def criticalPowerCoeff (α : ℝ) : ℕ → ℝ
  | 0 => -1
  | n + 1 => criticalPowerTail α n - criticalPowerTail α (n + 1)

theorem criticalPowerTail_pos (α : ℝ) (n : ℕ) : 0 < criticalPowerTail α n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem criticalPowerTail_zero (α : ℝ) : criticalPowerTail α 0 = 1 := by
  simp only [criticalPowerTail, Nat.cast_zero, zero_add, Real.one_rpow]

theorem criticalPowerTail_antitone (α : ℝ) (hα : 0 ≤ α) : Antitone (criticalPowerTail α) := by
  intro m n hmn
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hmn 1) (neg_nonpos.mpr hα)

theorem criticalPowerTail_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (criticalPowerTail α) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) atTop (𝓝 0)
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    h.comp (tendsto_add_atTop_nat 1)

/-- Every signed partial sum is exactly the negative remaining power tail. -/
theorem criticalPowerCoeff_partialSum (α : ℝ) (M : ℕ) :
    (∑ r ∈ range (M + 1), criticalPowerCoeff α r) = -criticalPowerTail α M := by
  induction M with
  | zero => simp [criticalPowerCoeff, criticalPowerTail_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, criticalPowerCoeff]
    ring

theorem criticalPowerCoeff_abs_partialSum (α : ℝ) (hα : 0 ≤ α) (M : ℕ) :
    (∑ r ∈ range (M + 1), |criticalPowerCoeff α r|) = 2 - criticalPowerTail α M := by
  induction M with
  | zero => norm_num [criticalPowerCoeff, criticalPowerTail_zero]
  | succ M ih =>
    have hn : 0 ≤ criticalPowerCoeff α (M + 1) :=
      sub_nonneg.mpr (criticalPowerTail_antitone α hα (Nat.le_succ M))
    rw [Finset.sum_range_succ, ih, abs_of_nonneg hn, criticalPowerCoeff]
    ring

/-- Nonnegative power exponents always have absolutely summable coefficient differences. -/
theorem summable_abs_criticalPowerCoeff (α : ℝ) (hα : 0 ≤ α) :
    Summable (fun r => |criticalPowerCoeff α r|) := by
  apply summable_of_sum_range_le (fun r => abs_nonneg _) (c := 2)
  intro N
  cases N with
  | zero => simp
  | succ M =>
    rw [criticalPowerCoeff_abs_partialSum α hα]
    exact sub_le_self _ (criticalPowerTail_pos α M).le

/-- Every positive exponent has exactly the same absolute coefficient mass. -/
theorem tsum_abs_criticalPowerCoeff (α : ℝ) (hα : 0 < α) :
    (∑' r, |criticalPowerCoeff α r|) = 2 := by
  have hsum : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), |criticalPowerCoeff α r|)
      atTop (𝓝 (∑' r, |criticalPowerCoeff α r|)) :=
    (summable_abs_criticalPowerCoeff α hα.le).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
  have htail : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), |criticalPowerCoeff α r|)
      atTop (𝓝 2) := by
    simp only [criticalPowerCoeff_abs_partialSum α hα.le]
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub
        (criticalPowerTail_tendsto α hα)
  exact tendsto_nhds_unique hsum htail

/-- Every positive exponent has zero total coefficient evaluation. -/
theorem tsum_criticalPowerCoeff (α : ℝ) (hα : 0 < α) :
    (∑' r, criticalPowerCoeff α r) = 0 := by
  have hsum : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), criticalPowerCoeff α r)
      atTop (𝓝 (∑' r, criticalPowerCoeff α r)) :=
    (summable_abs_criticalPowerCoeff α hα.le).of_abs.hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
  have htail : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), criticalPowerCoeff α r)
      atTop (𝓝 0) := by
    simp only [criticalPowerCoeff_partialSum]
    simpa only [neg_zero] using (criticalPowerTail_tendsto α hα).neg
  exact tendsto_nhds_unique hsum htail

theorem criticalPowerTail_sq (α : ℝ) (M : ℕ) :
    criticalPowerTail α M ^ 2 = ((M : ℝ) + 1) ^ (-(2 * α)) := by
  rw [criticalPowerTail, pow_two, ← Real.rpow_add (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
  congr 1
  ring

/-- The exact square-partial-sum threshold is one half. -/
theorem summable_sq_criticalPowerCoeff_partialSum_iff (α : ℝ) :
    Summable (fun M => (∑ r ∈ range (M + 1), criticalPowerCoeff α r) ^ 2) ↔
      (1 : ℝ) / 2 < α := by
  simp only [criticalPowerCoeff_partialSum, neg_sq, criticalPowerTail_sq]
  have hs : Summable (fun M : ℕ => ((M : ℝ) + 1) ^ (-(2 * α))) ↔
      Summable (fun M : ℕ => (M : ℝ) ^ (-(2 * α))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1 (f := fun M : ℕ => (M : ℝ) ^ (-(2 * α))))
  rw [hs, Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith only [h]

end GaloisForLFunctions.BiarithmeticGeometry

