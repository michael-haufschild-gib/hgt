import GaloisForLFunctions.HTGeometry.KleinGordonFlatBandPotential

/-!
# An exactly periodic clock

On the band where the flattening potential makes the shifted frequency one, the shifted propagator is
multiplication by the scalars `cos t` and `sin t`. The closed form of the solution then reads

`u(t) = (cos t)Px + (sin t)Py`,   `u̇(t) = −(sin t)Px + (cos t)Py`,

so the clock is exactly `2π`-periodic and returns to its initial state at `t = 2π`. This is a genuine
bounded real potential — not a limiting or degenerate case — in which a clock repeats itself exactly.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section PeriodicClock

variable {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **On the flat band the shifted cosine propagator is the scalar `cos t`.** -/
theorem kgShiftedCosOp_kgFlatPot (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedCosOp (measurable_kgFlatPot (E := E) b).neg t (kgLowPassOp (Real.sqrt b) x)
      = ((Real.cos t : ℝ) : ℂ) • kgLowPassOp (Real.sqrt b) x := by
  have hprod : Measurable fun ξ : E =>
      kgShiftedCos (fun ζ : E => -(kgFlatPot b ζ)) t ξ * kgLowPass (Real.sqrt b) ξ :=
    (measurable_kgShiftedCos (measurable_kgFlatPot b).neg t).mul
      (measurable_kgLowPass (Real.sqrt b))
  have hprodb : ∀ ξ : E, ‖kgShiftedCos (fun ζ : E => -(kgFlatPot b ζ)) t ξ
      * kgLowPass (Real.sqrt b) ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le _ t ξ) (norm_nonneg _)
      (norm_kgLowPass_le (Real.sqrt b) ξ)
  have hconst : Measurable fun ξ : E =>
      ((Real.cos t : ℝ) : ℂ) * kgLowPass (Real.sqrt b) ξ :=
    measurable_const.mul (measurable_kgLowPass (Real.sqrt b))
  have hconstb : ∀ ξ : E, ‖((Real.cos t : ℝ) : ℂ) * kgLowPass (Real.sqrt b) ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_one₀ (Real.abs_cos_le_one t) (norm_nonneg _)
      (norm_kgLowPass_le (Real.sqrt b) ξ)
  have hcomp : (kgShiftedCosOp (E := E) (measurable_kgFlatPot (E := E) b).neg t).comp
      (kgLowPassOp (Real.sqrt b)) = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgShiftedCosOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod zero_le_one hprodb = fourierMulCLM hconst zero_le_one hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedCos_kgFlatPot_lowPass (b := b) t))
  have hsmul : fourierMulCLM hconst zero_le_one hconstb
      = ((Real.cos t : ℝ) : ℂ) • kgLowPassOp (E := E) (Real.sqrt b) := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one (norm_kgLowPass_le (Real.sqrt b)) zero_le_one
      hconstb _ (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **On the flat band the shifted sine propagator is the scalar `sin t`.** -/
theorem kgShiftedSinFreqOp_kgFlatPot (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedSinFreqOp (measurable_kgFlatPot (E := E) b).neg t (kgLowPassOp (Real.sqrt b) x)
      = ((Real.sin t : ℝ) : ℂ) • kgLowPassOp (Real.sqrt b) x := by
  have hprod : Measurable fun ξ : E =>
      kgShiftedSinOverFreq (fun ζ : E => -(kgFlatPot b ζ)) t ξ * kgLowPass (Real.sqrt b) ξ :=
    (measurable_kgShiftedSinOverFreq (measurable_kgFlatPot b).neg t).mul
      (measurable_kgLowPass (Real.sqrt b))
  have hprodb : ∀ ξ : E, ‖kgShiftedSinOverFreq (fun ζ : E => -(kgFlatPot b ζ)) t ξ
      * kgLowPass (Real.sqrt b) ξ‖ ≤ |t| := by
    intro ξ
    rw [norm_mul]
    calc ‖kgShiftedSinOverFreq (fun ζ : E => -(kgFlatPot b ζ)) t ξ‖ * ‖kgLowPass (Real.sqrt b) ξ‖
        ≤ |t| * 1 := mul_le_mul (norm_kgShiftedSinOverFreq_le _ t ξ)
          (norm_kgLowPass_le (Real.sqrt b) ξ) (norm_nonneg _) (abs_nonneg t)
      _ = |t| := mul_one _
  have hconst : Measurable fun ξ : E =>
      ((Real.sin t : ℝ) : ℂ) * kgLowPass (Real.sqrt b) ξ :=
    measurable_const.mul (measurable_kgLowPass (Real.sqrt b))
  have hconstb : ∀ ξ : E, ‖((Real.sin t : ℝ) : ℂ) * kgLowPass (Real.sqrt b) ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_one₀ (Real.abs_sin_le_one t) (norm_nonneg _)
      (norm_kgLowPass_le (Real.sqrt b) ξ)
  have hcomp : (kgShiftedSinFreqOp (E := E) (measurable_kgFlatPot (E := E) b).neg t).comp
      (kgLowPassOp (Real.sqrt b)) = fourierMulCLM hprod (abs_nonneg t) hprodb := by
    rw [kgShiftedSinFreqOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ (abs_nonneg t) hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod (abs_nonneg t) hprodb
      = fourierMulCLM hconst zero_le_one hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedSinOverFreq_kgFlatPot_lowPass (b := b) t))
  have hsmul : fourierMulCLM hconst zero_le_one hconstb
      = ((Real.sin t : ℝ) : ℂ) • kgLowPassOp (E := E) (Real.sqrt b) := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one (norm_kgLowPass_le (Real.sqrt b)) zero_le_one
      hconstb _ (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **The clock of the flattening potential is a plane rotation.** -/
theorem kgShiftedField_kgFlatPot (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedField (measurable_kgFlatPot (E := E) b) (Real.sqrt b) x y t
      = ((Real.cos t : ℝ) : ℂ) • kgLowPassOp (Real.sqrt b) x
        + ((Real.sin t : ℝ) : ℂ) • kgLowPassOp (Real.sqrt b) y := by
  rw [kgShiftedField, kgShiftedCosOp_kgFlatPot, kgShiftedSinFreqOp_kgFlatPot]

set_option maxHeartbeats 1000000 in
/-- **The clock is exactly `2π`-periodic.** -/
theorem kgShiftedField_kgFlatPot_periodic (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedField (measurable_kgFlatPot (E := E) b) (Real.sqrt b) x y (t + 2 * Real.pi)
      = kgShiftedField (measurable_kgFlatPot (E := E) b) (Real.sqrt b) x y t := by
  rw [kgShiftedField_kgFlatPot, kgShiftedField_kgFlatPot,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

set_option maxHeartbeats 1000000 in
/-- **The clock returns exactly to its initial state after one period.** -/
theorem kgShiftedField_kgFlatPot_two_pi (x y : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedField (measurable_kgFlatPot (E := E) b) (Real.sqrt b) x y (2 * Real.pi)
      = kgLowPassOp (Real.sqrt b) x := by
  rw [kgShiftedField_kgFlatPot, Real.cos_two_pi, Real.sin_two_pi]
  simp

end PeriodicClock

end GaloisForLFunctions.HTGeometry
