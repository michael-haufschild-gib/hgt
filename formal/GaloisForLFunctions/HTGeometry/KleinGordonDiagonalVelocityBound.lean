import GaloisForLFunctions.HTGeometry.KleinGordonDiagonalNoDrift

/-!
# The velocity of a diagonal clock is bounded too

The generator is bounded on a band and the sine propagator is bounded uniformly in time, so the
velocity of the closed-form solution is bounded uniformly in time as well:

`‖u̇(t)‖ ≤ (1 + R² + b)/√(1−b) · ‖Px‖ + ‖Py‖`.

With the bound on the field this says a clock in a weak real diagonal background drifts in neither
position nor velocity, however long it runs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section VelocityBound

variable {p : E → ℝ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The velocity of a diagonal clock is bounded uniformly in time.** -/
theorem norm_kgShiftedVel_le (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgShiftedVel hp hb0 hb1 hpb R x y t‖
      ≤ (1 + R ^ 2 + b) * (1 / Real.sqrt (1 - b)) * ‖kgLowPassOp R x‖
        + ‖kgLowPassOp R y‖ := by
  have hband := band_bound_nonneg (b := b) hb0 R
  have hinv : (0 : ℝ) ≤ 1 / Real.sqrt (1 - b) := by positivity
  have hsin : ‖kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x)‖
      ≤ 1 / Real.sqrt (1 - b) * ‖kgLowPassOp R x‖ :=
    ContinuousLinearMap.le_of_opNorm_le _
      (norm_kgShiftedSinFreqOp_le_inv hp.neg hb1 (abs_neg_pot_le hpb) t) _
  have hgen : ‖kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
        (kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x))‖
      ≤ (1 + R ^ 2 + b) * ‖kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x)‖ :=
    ContinuousLinearMap.le_of_opNorm_le _
      (norm_kgShiftedFreqSqLowOp_le hp.neg hb0 hb1 (abs_neg_pot_le hpb) R) _
  have hchain : ‖kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
        (kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x))‖
      ≤ (1 + R ^ 2 + b) * (1 / Real.sqrt (1 - b)) * ‖kgLowPassOp R x‖ := by
    have hstep := mul_le_mul_of_nonneg_left hsin hband
    calc ‖kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
            (kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x))‖
        ≤ (1 + R ^ 2 + b) * ‖kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x)‖ := hgen
      _ ≤ (1 + R ^ 2 + b) * (1 / Real.sqrt (1 - b) * ‖kgLowPassOp R x‖) := hstep
      _ = (1 + R ^ 2 + b) * (1 / Real.sqrt (1 - b)) * ‖kgLowPassOp R x‖ := by ring
  have hcos : ‖kgShiftedCosOp hp.neg t (kgLowPassOp R y)‖ ≤ ‖kgLowPassOp R y‖ := by
    have h := ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedCosOp_le hp.neg t)
      (kgLowPassOp R y)
    linarith
  rw [kgShiftedVel]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  linarith

set_option maxHeartbeats 1000000 in
/-- **A diagonal clock drifts in neither position nor velocity.** -/
theorem norm_kgShiftedField_and_vel_le (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgShiftedField hp R x y t‖
        ≤ ‖kgLowPassOp R x‖ + 1 / Real.sqrt (1 - b) * ‖kgLowPassOp R y‖
      ∧ ‖kgShiftedVel hp hb0 hb1 hpb R x y t‖
        ≤ (1 + R ^ 2 + b) * (1 / Real.sqrt (1 - b)) * ‖kgLowPassOp R x‖
          + ‖kgLowPassOp R y‖ :=
  ⟨norm_kgShiftedField_le hp hb1 hpb R x y t, norm_kgShiftedVel_le hp hb0 hb1 hpb R x y t⟩

end VelocityBound

end GaloisForLFunctions.HTGeometry
