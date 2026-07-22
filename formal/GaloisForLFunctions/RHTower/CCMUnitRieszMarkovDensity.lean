import GaloisForLFunctions.RHTower.CCMCriticalMellinApertureResolvent
import GaloisForLFunctions.RHTower.MobiusLogDivisorParaproduct

/-!
# The unit-Riesz aperture profile has a positive Markov density

On the logarithmic cell `log m ≤ v < log (m + 1)`, the unit-Riesz profile is

`3 m exp (-v) - 3 (sum_{r=1}^m sqrt r) exp (-3v/2)`.

Its derivative is nonnegative.  The arithmetic engine is the sharp prefix inequality

`2 m sqrt (m + 1) ≤ 3 sum_{r=1}^m sqrt r`.

This is the finite, unconditional positivity core of the paper-level Markov--virial
factorization.  The global absolute-continuity, Laplace-transform, and Landau statements remain
paper theorems; they are not claimed by this module.
-/

open Nat Finset
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Square-root prefix mass `sum_{r=1}^m sqrt r`. -/
def unitRieszSqrtPrefixMass (m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m, Real.sqrt (r + 1)

/-- The exact prefix inequality forcing monotonicity of the logarithmic unit-Riesz profile. -/
theorem unitRieszSqrtPrefixMass_lower (m : ℕ) :
    2 * (m : ℝ) * Real.sqrt (m + 1) ≤ 3 * unitRieszSqrtPrefixMass m := by
  induction m with
  | zero => simp [unitRieszSqrtPrefixMass]
  | succ m ih =>
      have hs1 : 0 ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
      have hs2 : 0 ≤ Real.sqrt ((m : ℝ) + 2) := Real.sqrt_nonneg _
      have hs1sq : (Real.sqrt ((m : ℝ) + 1)) ^ 2 = (m : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hs2sq : (Real.sqrt ((m : ℝ) + 2)) ^ 2 = (m : ℝ) + 2 :=
        Real.sq_sqrt (by positivity)
      have hsq :
          (2 * ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 2)) ^ 2 ≤
            ((2 * (m : ℝ) + 3) * Real.sqrt ((m : ℝ) + 1)) ^ 2 := by
        simp only [mul_pow, hs1sq, hs2sq]
        nlinarith
      have hstep :
          2 * ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 2) ≤
            (2 * (m : ℝ) + 3) * Real.sqrt ((m : ℝ) + 1) :=
        (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
      rw [unitRieszSqrtPrefixMass, sum_range_succ]
      rw [unitRieszSqrtPrefixMass] at ih
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      ring_nf at ih hstep ⊢
      nlinarith

/-- Unit-Riesz logarithmic profile on the cell with `m` active progression atoms. -/
def unitRieszCellProfile (m : ℕ) (v : ℝ) : ℝ :=
  3 * m * Real.exp (-v) -
    3 * unitRieszSqrtPrefixMass m * Real.exp (-3 * v / 2)

/-- Candidate Markov density: derivative of `unitRieszCellProfile`. -/
def unitRieszCellMarkovDensity (m : ℕ) (v : ℝ) : ℝ :=
  -3 * m * Real.exp (-v) +
    (9 / 2 : ℝ) * unitRieszSqrtPrefixMass m * Real.exp (-3 * v / 2)

/-- Exact derivative formula on every logarithmic cell. -/
theorem hasDerivAt_unitRieszCellProfile (m : ℕ) (v : ℝ) :
    HasDerivAt (unitRieszCellProfile m) (unitRieszCellMarkovDensity m v) v := by
  unfold unitRieszCellProfile unitRieszCellMarkovDensity
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-v)) v := by
    simpa only [Function.comp_apply, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-3 * x / 2))
      ((-3 / 2) * Real.exp (-3 * v / 2)) v := by
    convert
      (Real.hasDerivAt_exp (-3 * v / 2)).comp v
        (((hasDerivAt_id v).const_mul (-3)).div_const 2) using 1 <;> ring
  convert (h1.const_mul (3 * (m : ℝ))).sub
    (h2.const_mul (3 * unitRieszSqrtPrefixMass m)) using 1 <;> ring

/-- The cell derivative is nonnegative throughout the physical logarithmic cell.  The hypothesis
is exactly the upper cell boundary `exp (v/2) ≤ sqrt (m+1)`. -/
theorem unitRieszCellMarkovDensity_nonneg
    (m : ℕ) (v : ℝ)
    (hv : Real.exp (v / 2) ≤ Real.sqrt (m + 1)) :
    0 ≤ unitRieszCellMarkovDensity m v := by
  have hprefix := unitRieszSqrtPrefixMass_lower m
  have hempos : 0 < Real.exp (-v) := Real.exp_pos _
  have hehalfpos : 0 < Real.exp (-v / 2) := Real.exp_pos _
  have hinv : Real.exp (-v / 2) * Real.exp (v / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hcell :
      2 * (m : ℝ) ≤
        3 * unitRieszSqrtPrefixMass m * Real.exp (-v / 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * (m : ℝ))
    have hcombined :
        2 * (m : ℝ) * Real.exp (v / 2) ≤
          3 * unitRieszSqrtPrefixMass m := hscaled.trans hprefix
    calc
      2 * (m : ℝ) =
          (2 * (m : ℝ) * Real.exp (v / 2)) * Real.exp (-v / 2) := by
            rw [mul_assoc, mul_comm (Real.exp (v / 2)), hinv]
            ring
      _ ≤ (3 * unitRieszSqrtPrefixMass m) * Real.exp (-v / 2) :=
        mul_le_mul_of_nonneg_right hcombined hehalfpos.le
  rw [unitRieszCellMarkovDensity]
  have hexp_split : Real.exp (-3 * v / 2) =
      Real.exp (-v) * Real.exp (-v / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp_split]
  have hscaled := mul_le_mul_of_nonneg_right hcell
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hempos.le)
  nlinarith

end

end RHTower
