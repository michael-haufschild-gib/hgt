import GaloisForLFunctions.HTGeometry.KleinGordonShiftedStrongSolution

/-!
# The mild solution of a diagonal background in closed form

The corpus builds the solution of the band problem as a mild solution of the Duhamel equation. For a
real frequency-diagonal potential that solution is the shifted propagator: both are strong solutions
of the same band problem with the same data, and that problem has only one solution.

So the Duhamel field is `cos(tΩ)Px + (sin(tΩ)/Ω)Py`, and its velocity is the corresponding derivative
— the clock of a diagonal background is computed, not merely estimated.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Identification

variable {p : E → ℝ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The mild field of a real diagonal potential on a band is the shifted propagator.** -/
theorem kgFieldMildT_eq_kgShiftedField (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
          (norm_kgRealPotSymbol_le hpb)) R)
        (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t
      = kgShiftedField hp R x y t := by
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => fourierMulCLM (E := E) (measurable_kgRealPotSymbol hp) hb0
      (norm_kgRealPotSymbol_le hpb)) r‖ ≤ b := fun _ => norm_fourierMulCLM_le _ _ _
  have hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
        (norm_kgRealPotSymbol_le hpb)) r z := fun _ => continuous_const
  have hRb := norm_kgBandOpT_le hb0 hWb R
  have hRs := continuous_kgBandOpT_apply hWs R
  refine eq_kgShiftedField_of_solvesKGSourceT hp hb0 hb1 hpb R x y
    (solvesKGSourceT_band hb0 hWb hWs R x y) ?_ ?_ t
  · rw [kgFieldMildT_zero hb0 hRb hRs, kgFreqInvOp_kgFreqLowOp]
  · rw [kgFieldVelT, intervalIntegral.integral_same, kgSinOp_zero, kgCosOp_zero]
    simp

set_option maxHeartbeats 1000000 in
/-- **The mild velocity is the shifted velocity.** -/
theorem kgFieldVelT_eq_kgShiftedVel (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
          (norm_kgRealPotSymbol_le hpb)) R) (kgFreqLowOp R x) (kgLowPassOp R y) t
      = kgShiftedVel hp hb0 hb1 hpb R x y t := by
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => fourierMulCLM (E := E) (measurable_kgRealPotSymbol hp) hb0
      (norm_kgRealPotSymbol_le hpb)) r‖ ≤ b := fun _ => norm_fourierMulCLM_le _ _ _
  have hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
        (norm_kgRealPotSymbol_le hpb)) r z := fun _ => continuous_const
  have hsolve := solvesKGSourceT_band (W := fun _ : ℝ => fourierMulCLM
    (measurable_kgRealPotSymbol hp) hb0 (norm_kgRealPotSymbol_le hpb)) hb0 hWb hWs R x y
  have hfun : kgFieldMildT (kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol hp) hb0 (norm_kgRealPotSymbol_le hpb)) R)
      (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) = kgShiftedField hp R x y :=
    funext fun s => kgFieldMildT_eq_kgShiftedField hp hb0 hb1 hpb R x y s
  have hderiv := hsolve.1 t
  rw [hfun] at hderiv
  exact hderiv.unique (hasDerivAt_kgShiftedField hp hb0 hb1 hpb R x y t)

end Identification

end GaloisForLFunctions.HTGeometry
