import GaloisForLFunctions.HTGeometry.FokasLenellsOrbitDecay

/-!
# Oscillatory testing of the constructed diagonal columns

An arbitrary Schwartz coefficient can replace the original off-diagonal
coefficient in the integration-by-parts argument. This supplies the source
estimate for a second spectral-power correction, whose endpoint terms
cancel between the two sides of the actual scattering matrix.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def diagonalTestAmplitude (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  a x*diagonalOrbit f g h z left upper x

def diagonalTestRate (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  SchwartzMap.derivCLM ℂ ℂ a x*diagonalOrbit f g h z left upper x+
    a x*diagonalOrbitRate f g h z left upper x

theorem diagonalTestAmplitude_hasDerivAt (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    HasDerivAt (diagonalTestAmplitude f g h a z left upper) (diagonalTestRate f g h a z left upper x) x := by
  change HasDerivAt (fun y => a y*diagonalOrbit f g h z left upper y) (diagonalTestRate f g h a z left upper x) x
  simpa only [diagonalTestRate,SchwartzMap.derivCLM_apply] using
    (a.hasDerivAt x).fun_mul (diagonalOrbit_hasDerivAt f g h z left upper x)

theorem diagonalTestAmplitude_continuous (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (diagonalTestAmplitude f g h a z left upper) :=
  a.continuous.mul (diagonalOrbit_continuous f g h z left upper)

theorem diagonalTestRate_continuous (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (diagonalTestRate f g h a z left upper) :=
  ((SchwartzMap.derivCLM ℂ ℂ a).continuous.mul (diagonalOrbit_continuous f g h z left upper)).add
    (a.continuous.mul (diagonalOrbitRate_continuous f g h z left upper))

def diagonalTestMajor (f g h a : SchwartzMap ℝ ℂ) (left : Bool) (x : ℝ) : ℝ :=
  (‖SchwartzMap.derivCLM ℂ ℂ a x‖+‖a.toBoundedContinuousFunction‖*orientedEffectiveDensity f g h left x)*
    Real.exp (effectiveMass f g h)

theorem diagonalTestMajor_nonneg (f g h a : SchwartzMap ℝ ℂ) (left : Bool) (x : ℝ) :
    0 ≤ diagonalTestMajor f g h a left x := by
  unfold diagonalTestMajor
  positivity [orientedEffectiveDensity_nonneg f g h left x]

theorem diagonalTestMajor_continuous (f g h a : SchwartzMap ℝ ℂ) (left : Bool) :
    Continuous (diagonalTestMajor f g h a left) :=
  (((SchwartzMap.derivCLM ℂ ℂ a).continuous.norm).add
    ((orientedEffectiveDensity_continuous f g h left).const_mul _)).mul_const _

theorem diagonalTestMajor_integrable (f g h a : SchwartzMap ℝ ℂ) (left : Bool) :
    Integrable (diagonalTestMajor f g h a left) :=
  (((SchwartzMap.derivCLM ℂ ℂ a).integrable.norm).add
    ((orientedEffectiveDensity_integrable f g h left).const_mul _)).mul_const _

theorem diagonalTestRate_bound (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖diagonalTestRate f g h a z left upper |x|‖ ≤ diagonalTestMajor f g h a left |x| := by
  have ha := a.toBoundedContinuousFunction.norm_coe_le_norm |x|
  have hd := (offOrbit_coordinates_bound f g h z left upper x).2
  have hr := diagonalOrbitRate_bound f g h z left upper x
  calc
    _ ≤ ‖SchwartzMap.derivCLM ℂ ℂ a |x|‖*‖diagonalOrbit f g h z left upper |x|‖+
        ‖a |x|‖*‖diagonalOrbitRate f g h z left upper |x|‖ := by
      simpa only [diagonalTestRate,norm_mul] using norm_add_le
        (SchwartzMap.derivCLM ℂ ℂ a |x| *diagonalOrbit f g h z left upper |x|)
        (a |x| *diagonalOrbitRate f g h z left upper |x|)
    _ ≤ ‖SchwartzMap.derivCLM ℂ ℂ a |x|‖*Real.exp (effectiveMass f g h)+
        ‖a.toBoundedContinuousFunction‖*(orientedEffectiveDensity f g h left |x| *Real.exp (effectiveMass f g h)) :=
      add_le_add (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (mul_le_mul ha hr (norm_nonneg _) (norm_nonneg _))
    _ = _ := by unfold diagonalTestMajor; ring

/-- A finite source bound independent of real frequency and distance along either oriented half-line. -/
def diagonalTestBudget (f g h a : SchwartzMap ℝ ℂ) (left : Bool) : ℝ :=
  2*(‖a.toBoundedContinuousFunction‖*Real.exp (effectiveMass f g h))+
    ∫ x, diagonalTestMajor f g h a left x

theorem diagonalTestBudget_nonneg (f g h a : SchwartzMap ℝ ℂ) (left : Bool) :
    0 ≤ diagonalTestBudget f g h a left := by
  have hi : 0 ≤ ∫ x, diagonalTestMajor f g h a left x :=
    MeasureTheory.integral_nonneg (diagonalTestMajor_nonneg f g h a left)
  unfold diagonalTestBudget
  positivity

def diagonalTestSource (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..x, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*diagonalTestAmplitude f g h a z left upper s

/-- The multiplied integration-by-parts identity is valid for either frequency sign and at zero. -/
theorem diagonalTestSource_ibp (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    (-(I*(offOrbitFrequency z left upper:ℂ)))*diagonalTestSource f g h a z left upper x =
      FDNLS.staggerPhase (offOrbitFrequency z left upper) x*diagonalTestAmplitude f g h a z left upper x-
        diagonalTestAmplitude f g h a z left upper 0-
        ∫ s in (0:ℝ)..x, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*diagonalTestRate f g h a z left upper s := by
  let ω := offOrbitFrequency z left upper
  have hp : Continuous (FDNLS.staggerPhase ω) := by unfold FDNLS.staggerPhase; fun_prop
  have hd (s : ℝ) : HasDerivAt (fun y => FDNLS.staggerPhase ω y*diagonalTestAmplitude f g h a z left upper y)
      (-(I*(ω:ℂ))*(FDNLS.staggerPhase ω s*diagonalTestAmplitude f g h a z left upper s)+
        FDNLS.staggerPhase ω s*diagonalTestRate f g h a z left upper s) s := by
    refine ((FDNLS.hasDerivAt_staggerPhase ω s).fun_mul (diagonalTestAmplitude_hasDerivAt f g h a z left upper s)).congr_deriv ?_
    ring
  have h1 : IntervalIntegrable (fun s => -(I*(ω:ℂ))*(FDNLS.staggerPhase ω s*diagonalTestAmplitude f g h a z left upper s)) volume 0 x :=
    ((hp.mul (diagonalTestAmplitude_continuous f g h a z left upper)).const_mul _).intervalIntegrable 0 x
  have h2 : IntervalIntegrable (fun s => FDNLS.staggerPhase ω s*diagonalTestRate f g h a z left upper s) volume 0 x :=
    (hp.mul (diagonalTestRate_continuous f g h a z left upper)).intervalIntegrable 0 x
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2,intervalIntegral.integral_const_mul] at hi
  have hz : FDNLS.staggerPhase ω 0 = 1 := by simp [FDNLS.staggerPhase]
  rw [hz,one_mul] at hi
  exact eq_sub_iff_add_eq.mpr hi

/-- A Schwartz test against either constructed diagonal channel gains one complete spectral power. -/
theorem diagonalTestSource_frequency_bound (f g h a : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    2*|z| *‖diagonalTestSource f g h a z left upper |x|‖ ≤ diagonalTestBudget f g h a left := by
  have hrem : ‖∫ s in (0:ℝ)..|x|, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*
      diagonalTestRate f g h a z left upper s‖ ≤ ∫ s, diagonalTestMajor f g h a left s := by
    calc
      _ ≤ ∫ s in (0:ℝ)..|x|, diagonalTestMajor f g h a left s := by
        apply intervalIntegral.norm_integral_le_of_norm_le (abs_nonneg x) _
          ((diagonalTestMajor_continuous f g h a left).intervalIntegrable 0 |x|)
        filter_upwards with s hs
        rw [norm_mul,FDNLS.norm_staggerPhase,one_mul]
        simpa only [abs_of_nonneg hs.1.le] using diagonalTestRate_bound f g h a z left upper s
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le (abs_nonneg x)]
        exact setIntegral_le_integral (diagonalTestMajor_integrable f g h a left)
          (Eventually.of_forall (diagonalTestMajor_nonneg f g h a left))
  have hb (y : ℝ) : ‖diagonalTestAmplitude f g h a z left upper |y|‖ ≤
      ‖a.toBoundedContinuousFunction‖*Real.exp (effectiveMass f g h) := by
    rw [diagonalTestAmplitude,norm_mul]
    exact mul_le_mul (a.toBoundedContinuousFunction.norm_coe_le_norm |y|)
      (offOrbit_coordinates_bound f g h z left upper y).2 (norm_nonneg _) (norm_nonneg _)
  have hi := congrArg norm (diagonalTestSource_ibp f g h a z left upper |x|)
  simp only [norm_mul,norm_neg,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,offOrbitFrequency_abs] at hi
  rw [hi]
  have hp : ‖FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *diagonalTestAmplitude f g h a z left upper |x|‖ =
      ‖diagonalTestAmplitude f g h a z left upper |x|‖ := by rw [norm_mul,FDNLS.norm_staggerPhase,one_mul]
  have h1 := norm_sub_le (FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *diagonalTestAmplitude f g h a z left upper |x|)
    (diagonalTestAmplitude f g h a z left upper 0)
  rw [hp] at h1
  have h2 := norm_sub_le (FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *diagonalTestAmplitude f g h a z left upper |x|-
    diagonalTestAmplitude f g h a z left upper 0)
    (∫ s in (0:ℝ)..|x|, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*diagonalTestRate f g h a z left upper s)
  have h0 := hb 0
  simp only [abs_zero] at h0
  unfold diagonalTestBudget
  linarith [hb x]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
