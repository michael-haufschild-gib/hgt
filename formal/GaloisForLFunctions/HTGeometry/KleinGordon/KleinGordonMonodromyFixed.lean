import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPeriodicClock

/-!
# The monodromy of the periodic clock fixes its band

The flattening potential turns the clock into a plane rotation on its band, so after one period both
the field and the velocity return to their initial values. In the energy-space language this says the
monodromy at `2π` fixes every band-limited state:

`M v = v`.

The eigen-class of the Floquet theory is therefore not empty: every nonzero band-limited datum is an
eigenvector of the monodromy with multiplier one, in a genuine bounded real potential.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section MonodromyFixed

variable {b : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On the flat band the generator symbol is the band symbol. -/
theorem kgShiftedFreqSqLow_kgFlatPot_lowPass (ξ : E) :
    kgShiftedFreqSqLow (fun ζ : E => -(kgFlatPot b ζ)) (Real.sqrt b) ξ
        * kgLowPass (Real.sqrt b) ξ
      = kgLowPass (Real.sqrt b) ξ := by
  rw [kgShiftedFreqSqLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedFreq_kgFlatPot hξ]
    norm_num
  · simp

/-- **On the flat band the generator is the identity.** -/
theorem kgShiftedFreqSqLowOp_kgFlatPot (hb0 : 0 ≤ b) (hb1 : b < 1)
    (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedFreqSqLowOp (measurable_kgFlatPot (E := E) b).neg hb0 hb1
        (abs_neg_pot_le (abs_kgFlatPot_le hb0)) (Real.sqrt b) (kgLowPassOp (Real.sqrt b) x)
      = kgLowPassOp (Real.sqrt b) x := by
  have hband := band_bound_nonneg (b := b) hb0 (Real.sqrt b)
  have hprod : Measurable fun ξ : E =>
      kgShiftedFreqSqLow (fun ζ : E => -(kgFlatPot b ζ)) (Real.sqrt b) ξ
        * kgLowPass (Real.sqrt b) ξ :=
    (measurable_kgShiftedFreqSqLow (measurable_kgFlatPot b).neg (Real.sqrt b)).mul
      (measurable_kgLowPass (Real.sqrt b))
  have hprodb : ∀ ξ : E, ‖kgShiftedFreqSqLow (fun ζ : E => -(kgFlatPot b ζ)) (Real.sqrt b) ξ
      * kgLowPass (Real.sqrt b) ξ‖ ≤ 1 := by
    intro ξ
    rw [kgShiftedFreqSqLow_kgFlatPot_lowPass ξ]
    exact norm_kgLowPass_le (Real.sqrt b) ξ
  have hcomp : (kgShiftedFreqSqLowOp (E := E) (measurable_kgFlatPot (E := E) b).neg hb0 hb1
        (abs_neg_pot_le (abs_kgFlatPot_le hb0)) (Real.sqrt b)).comp
        (kgLowPassOp (Real.sqrt b))
      = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgShiftedFreqSqLowOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod zero_le_one hprodb = kgLowPassOp (E := E) (Real.sqrt b) := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedFreqSqLow_kgFlatPot_lowPass (b := b)))
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq]

/-- **The velocity of the periodic clock is the rotated datum.** -/
theorem kgShiftedVel_kgFlatPot (hb0 : 0 ≤ b) (hb1 : b < 1)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedVel (measurable_kgFlatPot (E := E) b) hb0 hb1 (abs_kgFlatPot_le hb0)
        (Real.sqrt b) x y t
      = -(((Real.sin t : ℝ) : ℂ) • kgLowPassOp (Real.sqrt b) x)
        + ((Real.cos t : ℝ) : ℂ) • kgLowPassOp (Real.sqrt b) y := by
  rw [kgShiftedVel, kgShiftedSinFreqOp_kgFlatPot, kgShiftedCosOp_kgFlatPot, map_smul,
    kgShiftedFreqSqLowOp_kgFlatPot hb0 hb1]

/-- The velocity returns after one period. -/
theorem kgShiftedVel_kgFlatPot_two_pi (hb0 : 0 ≤ b) (hb1 : b < 1)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedVel (measurable_kgFlatPot (E := E) b) hb0 hb1 (abs_kgFlatPot_le hb0)
        (Real.sqrt b) x y (2 * Real.pi)
      = kgLowPassOp (Real.sqrt b) y := by
  rw [kgShiftedVel_kgFlatPot hb0 hb1, Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- **The monodromy of the periodic clock fixes every band-limited state.** -/
theorem kgMonodromy_kgFlatPot_fixed (hb0 : 0 ≤ b) (hb1 : b < 1)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    kgFieldStateT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
          (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b))
        (kgFreqLowOp (Real.sqrt b) x) (kgLowPassOp (Real.sqrt b) y) (2 * Real.pi)
      = kgPair E (kgFreqLowOp (Real.sqrt b) x, kgLowPassOp (Real.sqrt b) y) := by
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
      (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) r‖ ≤ b :=
    fun _ => norm_fourierMulCLM_le _ _ _
  have hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b))
        hb0 (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) r z := fun _ => continuous_const
  have hBandb := norm_kgBandOpT_le hb0 hWb (Real.sqrt b)
  have hBands := continuous_kgBandOpT_apply hWs (Real.sqrt b)
  -- the field returns
  have hmild := kgFieldMildT_eq_kgShiftedField (measurable_kgFlatPot (E := E) b) hb0 hb1
    (abs_kgFlatPot_le hb0) (Real.sqrt b) x y (2 * Real.pi)
  rw [kgShiftedField_kgFlatPot_two_pi] at hmild
  have hgradinv := kgFreqInvOp_kgFieldGradT hb0 hBandb hBands
    (kgFreqLowOp (Real.sqrt b) x) (kgLowPassOp (Real.sqrt b) y) (2 * Real.pi)
  have hgrad : kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgFlatPot (E := E) b)) hb0
        (norm_kgRealPotSymbol_le (abs_kgFlatPot_le hb0))) (Real.sqrt b))
      (kgFreqLowOp (Real.sqrt b) x) (kgLowPassOp (Real.sqrt b) y) (2 * Real.pi)
      = kgFreqLowOp (Real.sqrt b) x := by
    refine kgFreqInvOp_injective ?_
    rw [hgradinv, hmild, kgFreqInvOp_kgFreqLowOp]
  -- the velocity returns
  have hvel := kgFieldVelT_eq_kgShiftedVel (measurable_kgFlatPot (E := E) b) hb0 hb1
    (abs_kgFlatPot_le hb0) (Real.sqrt b) x y (2 * Real.pi)
  rw [kgShiftedVel_kgFlatPot_two_pi hb0 hb1] at hvel
  rw [kgFieldStateT, hgrad, hvel]

end MonodromyFixed

end GaloisForLFunctions.HTGeometry
