import GaloisForLFunctions.HilbertMetric.TransverseDegreePhase
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact curvature of the first transverse-degree phase crossing

This module connects the transverse Fano margin to the literal second derivative of the
logarithm of the graph determinant partition.  At degree five the balancing transverse square
is `5 / 3`.  For lowering charge `B` and top multiplicity `k`, the exact curvature is
`-B + 5k / 4`.  The full symmetric top in base dimension sixteen has
`17 B = 20 k`, so its limiting log-determinant curvature is exactly `5k / 68 > 0`.

The result is an unconditional finite-dimensional determinant theorem.  The separate passage
from this limiting graph determinant to a span of distinct coherent vectors remains an analytic
collision-convergence problem.
-/

open Filter

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-! ### The balanced degree-five determinant -/

/-- Degree-five transverse partition at the balancing squared amplitude `5 / 3`. -/
def fifthDegreeBalancedPartition (B k : ℕ) (t : ℝ) : ℝ :=
  transverseDegreePartition B k 5 (Real.sqrt (5 / 3)) t

/-- Expanded logarithm of the balanced degree-five partition on the positive scale ray. -/
def fifthDegreeBalancedLogModel (B k : ℕ) (t : ℝ) : ℝ :=
  (B : ℝ) * Real.log t +
    (k : ℝ) * Real.log (t ^ 5 + (5 / 3 : ℝ) * t)

/-- First derivative of the expanded logarithmic model. -/
def fifthDegreeBalancedLogDerivative (B k : ℕ) (t : ℝ) : ℝ :=
  (B : ℝ) / t +
    (k : ℝ) *
      ((5 : ℝ) * t ^ 4 + 5 / 3) / (t ^ 5 + (5 / 3 : ℝ) * t)

/-- The balanced partition is exactly the lower skeleton times the two-degree graph factor. -/
theorem fifthDegreeBalancedPartition_eq (B k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    fifthDegreeBalancedPartition B k t =
      t ^ B * (t ^ 5 + (5 / 3 : ℝ) * t) ^ k := by
  unfold fifthDegreeBalancedPartition transverseDegreePartition
  rw [det_transverseDegreeGram k 5 (Real.sqrt (5 / 3)) t ht]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 5 / 3)]

/-- On positive scales, the literal logarithm of the determinant equals its expanded model. -/
theorem log_fifthDegreeBalancedPartition_eq (B k : ℕ) (t : ℝ) (ht : 0 < t) :
    Real.log (fifthDegreeBalancedPartition B k t) =
      fifthDegreeBalancedLogModel B k t := by
  rw [fifthDegreeBalancedPartition_eq B k t ht.le]
  have hinner : 0 < t ^ 5 + (5 / 3 : ℝ) * t := by
    rw [show t ^ 5 + (5 / 3 : ℝ) * t = t * (t ^ 4 + 5 / 3) by ring]
    exact mul_pos ht
      (add_pos_of_nonneg_of_pos (pow_nonneg ht.le 4) (by positivity))
  rw [Real.log_mul (pow_ne_zero B (ne_of_gt ht))
    (pow_ne_zero k (ne_of_gt hinner))]
  rw [Real.log_pow, Real.log_pow]
  rfl

/-! ### Exact logarithmic curvature -/

theorem hasDerivAt_fifthDegreeBalancedLogModel (B k : ℕ) (t : ℝ)
    (ht : t ≠ 0) (hh : t ^ 5 + (5 / 3 : ℝ) * t ≠ 0) :
    HasDerivAt (fifthDegreeBalancedLogModel B k)
      (fifthDegreeBalancedLogDerivative B k t) t := by
  have hinner :
      HasDerivAt (fun s : ℝ => s ^ 5 + (5 / 3 : ℝ) * s)
        ((5 : ℝ) * t ^ 4 + 5 / 3) t := by
    simpa only [id_eq, mul_one, Nat.cast_ofNat] using
      (((hasDerivAt_id t).pow 5).add
        ((hasDerivAt_id t).const_mul (5 / 3 : ℝ)))
  have hleft := (Real.hasDerivAt_log ht).const_mul (B : ℝ)
  have hright := (hinner.log hh).const_mul (k : ℝ)
  unfold fifthDegreeBalancedLogModel fifthDegreeBalancedLogDerivative
  convert hleft.add hright using 1
  ring

theorem hasDerivAt_fifthDegreeBalancedLogDerivative_one (B k : ℕ) :
    HasDerivAt (fifthDegreeBalancedLogDerivative B k)
      (-(B : ℝ) + (5 / 4 : ℝ) * (k : ℝ)) 1 := by
  have hleft : HasDerivAt (fun t : ℝ => (B : ℝ) / t) (-(B : ℝ)) 1 := by
    simpa only [id_eq, one_mul, mul_one, one_pow, zero_mul, zero_sub, div_one] using
      ((hasDerivAt_const (1 : ℝ) (B : ℝ)).div (hasDerivAt_id 1) one_ne_zero)
  have hnum :
      HasDerivAt (fun t : ℝ => (5 : ℝ) * t ^ 4 + 5 / 3) 20 1 := by
    convert ((((hasDerivAt_id (1 : ℝ)).pow 4).const_mul 5).add_const (5 / 3)) using 1
    simp only [id_eq, one_pow, mul_one, Nat.cast_ofNat]
    ring
  have hden :
      HasDerivAt (fun t : ℝ => t ^ 5 + (5 / 3 : ℝ) * t) (20 / 3) 1 := by
    convert ((hasDerivAt_id (1 : ℝ)).pow 5).add
      ((hasDerivAt_id 1).const_mul (5 / 3 : ℝ)) using 1
    · simp only [id_eq, one_pow, mul_one, Nat.cast_ofNat]
      ring
  have hden_ne : (1 : ℝ) ^ 5 + (5 / 3 : ℝ) * 1 ≠ 0 := by
    positivity
  have hright := (hnum.div hden hden_ne).const_mul (k : ℝ)
  convert hleft.add hright using 1
  · funext t
    unfold fifthDegreeBalancedLogDerivative
    simp only [Pi.add_apply, Pi.div_apply]
    ring
  · ring_nf

/-- The expanded degree-five logarithmic model has curvature `-B + 5k/4` at unit scale. -/
theorem fifthDegreeBalancedLogModel_secondDerivative_one (B k : ℕ) :
    deriv (deriv (fifthDegreeBalancedLogModel B k)) 1 =
      -(B : ℝ) + (5 / 4 : ℝ) * (k : ℝ) := by
  have hpos : ∀ᶠ t in nhds (1 : ℝ), 0 < t := eventually_gt_nhds zero_lt_one
  have hderiv :
      (fun t => deriv (fifthDegreeBalancedLogModel B k) t)
        =ᶠ[nhds (1 : ℝ)] fifthDegreeBalancedLogDerivative B k := by
    filter_upwards [hpos] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hhpos : 0 < t ^ 5 + (5 / 3 : ℝ) * t := by
      rw [show t ^ 5 + (5 / 3 : ℝ) * t = t * (t ^ 4 + 5 / 3) by ring]
      exact mul_pos ht
        (add_pos_of_nonneg_of_pos (pow_nonneg ht.le 4) (by positivity))
    exact (hasDerivAt_fifthDegreeBalancedLogModel B k t ht0 (ne_of_gt hhpos)).deriv
  exact
    ((hasDerivAt_fifthDegreeBalancedLogDerivative_one B k).congr_of_eventuallyEq hderiv).deriv

/-- **Literal determinant-curvature connector.**  The logarithm of the balanced graph
determinant itself, not merely its Fano proxy, has curvature `-B + 5k/4` at unit scale. -/
theorem fifthDegreeBalancedPartition_log_secondDerivative_one (B k : ℕ) :
    deriv (deriv (fun t => Real.log (fifthDegreeBalancedPartition B k t))) 1 =
      -(B : ℝ) + (5 / 4 : ℝ) * (k : ℝ) := by
  have hpos : ∀ᶠ t in nhds (1 : ℝ), 0 < t := eventually_gt_nhds zero_lt_one
  have hderiv :
      (fun t => deriv (fun s => Real.log (fifthDegreeBalancedPartition B k s)) t)
        =ᶠ[nhds (1 : ℝ)] fifthDegreeBalancedLogDerivative B k := by
    filter_upwards [hpos] with t ht
    have hlocalPos : ∀ᶠ s in nhds t, 0 < s := eventually_gt_nhds ht
    have hlocalEq :
        (fun s => Real.log (fifthDegreeBalancedPartition B k s))
          =ᶠ[nhds t] fifthDegreeBalancedLogModel B k := by
      filter_upwards [hlocalPos] with s hs
      exact log_fifthDegreeBalancedPartition_eq B k s hs
    calc
      deriv (fun s => Real.log (fifthDegreeBalancedPartition B k s)) t =
          deriv (fifthDegreeBalancedLogModel B k) t := hlocalEq.deriv_eq
      _ = fifthDegreeBalancedLogDerivative B k t := by
        have ht0 : t ≠ 0 := ne_of_gt ht
        have hinner : 0 < t ^ 5 + (5 / 3 : ℝ) * t := by
          rw [show t ^ 5 + (5 / 3 : ℝ) * t = t * (t ^ 4 + 5 / 3) by ring]
          exact mul_pos ht
            (add_pos_of_nonneg_of_pos (pow_nonneg ht.le 4) (by positivity))
        exact
          (hasDerivAt_fifthDegreeBalancedLogModel B k t ht0 (ne_of_gt hinner)).deriv
  exact
    ((hasDerivAt_fifthDegreeBalancedLogDerivative_one B k).congr_of_eventuallyEq hderiv).deriv

/-! ### First full-symmetric crossing -/

/-- In base dimension sixteen, the full degree-five symmetric top has exact positive limiting
log-determinant curvature `5k/68`. -/
theorem fullTop_fifthDegreeBalanced_logCurvature :
    deriv (deriv (fun t => Real.log
      (fifthDegreeBalancedPartition (fullTopLoweringCharge 16 5)
        (fullTopCount 16 5) t))) 1 =
      (5 / 68 : ℝ) * (fullTopCount 16 5 : ℝ) := by
  rw [fifthDegreeBalancedPartition_log_secondDerivative_one]
  have hcross := fullTopLoweringCharge_cross 16 3
  change 17 * fullTopLoweringCharge 16 5 = 5 * 4 * fullTopCount 16 5 at hcross
  have hcrossReal :
      (17 : ℝ) * (fullTopLoweringCharge 16 5 : ℝ) =
        (5 : ℝ) * 4 * (fullTopCount 16 5 : ℝ) := by
    exact_mod_cast hcross
  linarith

/-- The first full-symmetric transverse crossing has strictly positive log-determinant
curvature. -/
theorem fullTop_fifthDegreeBalanced_logCurvature_pos :
    0 < deriv (deriv (fun t => Real.log
      (fifthDegreeBalancedPartition (fullTopLoweringCharge 16 5)
        (fullTopCount 16 5) t))) 1 := by
  rw [fullTop_fifthDegreeBalanced_logCurvature]
  have hkNat : 0 < fullTopCount 16 5 := by
    unfold fullTopCount
    exact Nat.choose_pos (by omega)
  have hk : (0 : ℝ) < (fullTopCount 16 5 : ℝ) := by
    exact_mod_cast hkNat
  exact mul_pos (by positivity) hk

end

end GaloisForLFunctions.HilbertMetric
