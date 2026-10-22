import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonEigenWitness

/-!
# A diagonal clock never drifts

The shifted frequency of a weak real diagonal potential is bounded below, `Ω ≥ √(1−b)`, so the sine
propagator is bounded by `1/√(1−b)` — uniformly in time, not merely by the elapsed time. The closed
form of the solution then bounds the field itself for all time:

`‖u(t)‖ ≤ ‖Px‖ + ‖Py‖/√(1−b)`.

The energy estimates of the card bound the pair `(⟨D⟩u, u̇)`; this bounds the field, and says that a
clock in such a background does not drift, however long it runs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section NoDrift

variable {v : E → ℝ} {b : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The shifted frequency is bounded below.** -/
theorem sqrt_one_sub_le_kgShiftedFreq (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) (ξ : E) :
    Real.sqrt (1 - b) ≤ kgShiftedFreq v ξ := by
  have hsq := one_sub_le_kgShiftedFreq_sq hb1 hvb ξ
  have hmono : Real.sqrt (1 - b) ≤ Real.sqrt (kgShiftedFreq v ξ ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (kgShiftedFreq_nonneg v ξ)] at hmono

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The shifted sine symbol is bounded uniformly in time.** -/
theorem norm_kgShiftedSinOverFreq_le_inv (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (t : ℝ) (ξ : E) :
    ‖kgShiftedSinOverFreq v t ξ‖ ≤ 1 / Real.sqrt (1 - b) := by
  have hpos : 0 < Real.sqrt (1 - b) := Real.sqrt_pos.mpr (by linarith)
  have hΩ : 0 < kgShiftedFreq v ξ := kgShiftedFreq_pos hb1 hvb ξ
  rw [kgShiftedSinOverFreq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hΩ]
  have hnum : |Real.sin (t * kgShiftedFreq v ξ)| ≤ 1 := Real.abs_sin_le_one _
  have hstep : |Real.sin (t * kgShiftedFreq v ξ)| / kgShiftedFreq v ξ
      ≤ 1 / kgShiftedFreq v ξ := by
    gcongr
  refine le_trans hstep ?_
  exact one_div_le_one_div_of_le hpos (sqrt_one_sub_le_kgShiftedFreq hb1 hvb ξ)

/-- **The shifted sine propagator is bounded uniformly in time.** -/
theorem norm_kgShiftedSinFreqOp_le_inv (hv : Measurable v) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (t : ℝ) :
    ‖kgShiftedSinFreqOp (E := E) hv t‖ ≤ 1 / Real.sqrt (1 - b) := by
  have hpos : 0 < Real.sqrt (1 - b) := Real.sqrt_pos.mpr (by linarith)
  have heq : kgShiftedSinFreqOp (E := E) hv t
      = fourierMulCLM (measurable_kgShiftedSinOverFreq hv t) (le_of_lt (by positivity))
        (norm_kgShiftedSinOverFreq_le_inv hb1 hvb t) := by
    rw [kgShiftedSinFreqOp]
    exact fourierMulCLM_congr _ _ _ _ _ _ (Eventually.of_forall fun _ => rfl)
  rw [heq]
  exact norm_fourierMulCLM_le _ _ _

/-- **A clock in a weak real diagonal potential does not drift**: its field is bounded for all
time. -/
theorem norm_kgShiftedField_le {p : E → ℝ} (hp : Measurable p) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgShiftedField hp R x y t‖
      ≤ ‖kgLowPassOp R x‖ + 1 / Real.sqrt (1 - b) * ‖kgLowPassOp R y‖ := by
  have hcos : ‖kgShiftedCosOp hp.neg t (kgLowPassOp R x)‖ ≤ ‖kgLowPassOp R x‖ := by
    have h := ContinuousLinearMap.le_of_opNorm_le _ (norm_kgShiftedCosOp_le hp.neg t)
      (kgLowPassOp R x)
    linarith
  have hsin : ‖kgShiftedSinFreqOp hp.neg t (kgLowPassOp R y)‖
      ≤ 1 / Real.sqrt (1 - b) * ‖kgLowPassOp R y‖ :=
    ContinuousLinearMap.le_of_opNorm_le _
      (norm_kgShiftedSinFreqOp_le_inv hp.neg hb1 (abs_neg_pot_le hpb) t) _
  rw [kgShiftedField]
  refine le_trans (norm_add_le _ _) ?_
  linarith

end NoDrift

end GaloisForLFunctions.HTGeometry
