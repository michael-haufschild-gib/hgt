import GaloisForLFunctions.RHTower.CCMCriticalMellinApertureResolvent
import GaloisForLFunctions.RHTower.MobiusLogDivisorParaproduct

/-!
# The unit-Riesz aperture profile has a positive Markov density

On the logarithmic cell `log m ≤ v < log (m + 1)`, the unit-Riesz profile is

`3 m exp (-v) - 3 (sum_{r=1}^m sqrt r) exp (-3v/2)`.

Its derivative is nonnegative.  The arithmetic engine is the sharp prefix inequality

`2 m sqrt (m + 1) ≤ 3 sum_{r=1}^m sqrt r`.

This is known-derived corpus infrastructure, not a novelty claim.  It closes the finite,
unconditional positivity and gluing core of the paper-level Markov--virial factorization so later
research cannot mistake this elementary layer for the RH frontier.  Global absolute continuity,
Laplace transform, and Landau statements are not claimed by this module.
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
      have hs1sq : (Real.sqrt ((m : ℝ) + 1)) ^ (2 : ℕ) = (m : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hs2sq : (Real.sqrt ((m : ℝ) + 2)) ^ (2 : ℕ) = (m : ℝ) + 2 :=
        Real.sq_sqrt (by positivity)
      have hsq :
          (2 * ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 2)) ^ (2 : ℕ) ≤
            ((2 * (m : ℝ) + 3) * Real.sqrt ((m : ℝ) + 1)) ^ (2 : ℕ) := by
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
    simpa only [Function.comp_apply, mul_neg, mul_one] using!
      (Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-3 * x / 2))
      ((-3 / 2) * Real.exp (-3 * v / 2)) v := by
    convert!
      (Real.hasDerivAt_exp (-3 * v / 2)).comp v
        (((hasDerivAt_id v).const_mul (-3)).div_const 2) using 1
    all_goals ring_nf
  convert! (h1.const_mul (3 * (m : ℝ))).sub
    (h2.const_mul (3 * unitRieszSqrtPrefixMass m)) using 1
  all_goals ring_nf

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

/-- Adjacent logarithmic cells glue exactly at their common boundary.  The hypothesis is the
exponential form of `v = log (m+1)` and avoids any choice of logarithm branch. -/
theorem unitRieszCellProfile_succ_eq_at_boundary
    (m : ℕ) (v : ℝ)
    (hv : Real.exp (v / 2) = Real.sqrt (m + 1)) :
    unitRieszCellProfile (m + 1) v = unitRieszCellProfile m v := by
  have hinv : Real.exp (-v / 2) * Real.exp (v / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hboundary :
      Real.sqrt (m + 1) * Real.exp (-v / 2) = 1 := by
    rw [← hv, mul_comm]
    exact hinv
  have hexp_split : Real.exp (-3 * v / 2) =
      Real.exp (-v) * Real.exp (-v / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp_split' : Real.exp (-(3 * v) / 2) =
      Real.exp (-v) * Real.exp (-v / 2) := by
    convert hexp_split using 1
    all_goals ring_nf
  unfold unitRieszCellProfile unitRieszSqrtPrefixMass
  rw [sum_range_succ]
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [hexp_split']
  ring_nf at hboundary ⊢
  have hboundaryScaled := congrArg
    (fun x : ℝ => x * Real.exp (-v) * 3) hboundary
  ring_nf at hboundaryScaled
  nlinarith [hboundaryScaled]

/-- The first logarithmic cell starts at zero, matching `W(1)=0`. -/
theorem unitRieszCellProfile_one_zero :
    unitRieszCellProfile 1 0 = 0 := by
  norm_num [unitRieszCellProfile, unitRieszSqrtPrefixMass]

/-- Global logarithmic unit-Riesz profile, assembled by the active progression count
`floor(exp v)`. -/
def unitRieszLogProfile (v : ℝ) : ℝ :=
  unitRieszCellProfile ⌊Real.exp v⌋₊ v

/-- On each physical cell the global profile reduces definitionally to its explicit cell
formula. -/
theorem unitRieszLogProfile_eq_cell
    {m : ℕ} {v : ℝ}
    (hlow : (m : ℝ) ≤ Real.exp v)
    (hhigh : Real.exp v < (m : ℝ) + 1) :
    unitRieszLogProfile v = unitRieszCellProfile m v := by
  rw [unitRieszLogProfile,
    (Nat.floor_eq_iff (Real.exp_nonneg v)).2 ⟨hlow, hhigh⟩]

/-- Global profile starts at zero. -/
theorem unitRieszLogProfile_zero :
    unitRieszLogProfile 0 = 0 := by
  norm_num [unitRieszLogProfile, unitRieszCellProfile_one_zero]

end

end RHTower
