import GaloisForLFunctions.HTGeometry.FokasLenellsOrbitEntries

/-!
# Oscillatory source decay for constructed Fokas–Lenells columns

The differentiated off-diagonal amplitude has an integrable majorant
independent of the spectral parameter. Integration by parts is written
without division by frequency, so its identity and weighted estimate hold
for both frequency signs and at zero. This transfers one power of the
spectral frequency onto Schwartz coefficient derivatives while retaining
uniform control on either oriented spatial half-line.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def offOrbitAmplitude (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  offOrbitCoefficient f g h left upper x*diagonalOrbit f g h z left upper x

def offOrbitAmplitudeRate (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper) x*diagonalOrbit f g h z left upper x+
    offOrbitCoefficient f g h left upper x*diagonalOrbitRate f g h z left upper x

theorem offOrbitAmplitude_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    HasDerivAt (offOrbitAmplitude f g h z left upper) (offOrbitAmplitudeRate f g h z left upper x) x := by
  change HasDerivAt (fun y => offOrbitCoefficient f g h left upper y*diagonalOrbit f g h z left upper y)
    (offOrbitAmplitudeRate f g h z left upper x) x
  simpa only [offOrbitAmplitudeRate, SchwartzMap.derivCLM_apply] using
    ((offOrbitCoefficient f g h left upper).hasDerivAt x).fun_mul
      (diagonalOrbit_hasDerivAt f g h z left upper x)

theorem offOrbitAmplitude_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (offOrbitAmplitude f g h z left upper) :=
  (offOrbitCoefficient f g h left upper).continuous.mul (diagonalOrbit_continuous f g h z left upper)

theorem offOrbitAmplitudeRate_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (offOrbitAmplitudeRate f g h z left upper) :=
  ((SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper)).continuous.mul
    (diagonalOrbit_continuous f g h z left upper)).add
      ((offOrbitCoefficient f g h left upper).continuous.mul (diagonalOrbitRate_continuous f g h z left upper))

def offOrbitCoefficientSize (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : ℝ :=
  ‖(offOrbitCoefficient f g h left upper).toBoundedContinuousFunction‖

theorem offOrbitCoefficientSize_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    0 ≤ offOrbitCoefficientSize f g h left upper := norm_nonneg _

theorem offOrbitCoefficient_bound (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) :
    ‖offOrbitCoefficient f g h left upper x‖ ≤ offOrbitCoefficientSize f g h left upper :=
  (offOrbitCoefficient f g h left upper).toBoundedContinuousFunction.norm_coe_le_norm x

def offOrbitAmplitudeMajor (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) : ℝ :=
  (‖SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper) x‖+
    offOrbitCoefficientSize f g h left upper*orientedEffectiveDensity f g h left x)*Real.exp (effectiveMass f g h)

theorem offOrbitAmplitudeMajor_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) :
    0 ≤ offOrbitAmplitudeMajor f g h left upper x := by
  unfold offOrbitAmplitudeMajor
  positivity [offOrbitCoefficientSize_nonneg f g h left upper, orientedEffectiveDensity_nonneg f g h left x]

theorem offOrbitAmplitudeMajor_continuous (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    Continuous (offOrbitAmplitudeMajor f g h left upper) :=
  (((SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper)).continuous.norm).add
    ((orientedEffectiveDensity_continuous f g h left).const_mul _)).mul_const _

theorem offOrbitAmplitudeMajor_integrable (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    Integrable (offOrbitAmplitudeMajor f g h left upper) :=
  (((SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper)).integrable.norm).add
    ((orientedEffectiveDensity_integrable f g h left).const_mul _)).mul_const _

theorem offOrbitAmplitude_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖offOrbitAmplitude f g h z left upper |x|‖ ≤
      offOrbitCoefficientSize f g h left upper*Real.exp (effectiveMass f g h) := by
  rw [offOrbitAmplitude, norm_mul]
  exact mul_le_mul (offOrbitCoefficient_bound f g h left upper |x|)
    (offOrbit_coordinates_bound f g h z left upper x).2 (norm_nonneg _) (offOrbitCoefficientSize_nonneg f g h left upper)

/-- A fixed integrable majorant controls the differentiated amplitude for every spectral frequency. -/
theorem offOrbitAmplitudeRate_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖offOrbitAmplitudeRate f g h z left upper |x|‖ ≤ offOrbitAmplitudeMajor f g h left upper |x| := by
  have hb := offOrbitCoefficient_bound f g h left upper |x|
  have hw := (offOrbit_coordinates_bound f g h z left upper x).2
  have hd := diagonalOrbitRate_bound f g h z left upper x
  unfold offOrbitAmplitudeRate offOrbitAmplitudeMajor
  calc
    _ ≤ ‖SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper) |x|‖*
        ‖diagonalOrbit f g h z left upper |x|‖+
      ‖offOrbitCoefficient f g h left upper |x|‖*‖diagonalOrbitRate f g h z left upper |x|‖ := by
      simpa only [norm_mul] using norm_add_le
        (SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper) |x| *diagonalOrbit f g h z left upper |x|)
        (offOrbitCoefficient f g h left upper |x| *diagonalOrbitRate f g h z left upper |x|)
    _ ≤ ‖SchwartzMap.derivCLM ℂ ℂ (offOrbitCoefficient f g h left upper) |x|‖*Real.exp (effectiveMass f g h)+
      offOrbitCoefficientSize f g h left upper*(orientedEffectiveDensity f g h left |x| * Real.exp (effectiveMass f g h)) :=
      add_le_add (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
        (mul_le_mul hb hd (norm_nonneg _) (offOrbitCoefficientSize_nonneg f g h left upper))
    _ = _ := by ring

def offOrbitAmplitudeBudget (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : ℝ :=
  2*(offOrbitCoefficientSize f g h left upper*Real.exp (effectiveMass f g h))+
    ∫ x, offOrbitAmplitudeMajor f g h left upper x

theorem offOrbitAmplitudeBudget_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    0 ≤ offOrbitAmplitudeBudget f g h left upper := by
  have hi : 0 ≤ ∫ x, offOrbitAmplitudeMajor f g h left upper x :=
    MeasureTheory.integral_nonneg (fun x => offOrbitAmplitudeMajor_nonneg f g h left upper x)
  have hs := offOrbitCoefficientSize_nonneg f g h left upper
  unfold offOrbitAmplitudeBudget
  positivity

def offOrbitSource (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..x, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*offOrbitAmplitude f g h z left upper s

/-- Integration by parts in multiplied form remains valid at frequency zero and for both frequency signs. -/
theorem offOrbitSource_ibp (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    (-(I*(offOrbitFrequency z left upper:ℂ)))*offOrbitSource f g h z left upper x =
      FDNLS.staggerPhase (offOrbitFrequency z left upper) x*offOrbitAmplitude f g h z left upper x-
        offOrbitAmplitude f g h z left upper 0-
        ∫ s in (0:ℝ)..x, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*offOrbitAmplitudeRate f g h z left upper s := by
  let ω := offOrbitFrequency z left upper
  have hp : Continuous (FDNLS.staggerPhase ω) := by unfold FDNLS.staggerPhase; fun_prop
  have hd (s : ℝ) : HasDerivAt (fun y => FDNLS.staggerPhase ω y*offOrbitAmplitude f g h z left upper y)
      (-(I*(ω:ℂ))*(FDNLS.staggerPhase ω s*offOrbitAmplitude f g h z left upper s)+
        FDNLS.staggerPhase ω s*offOrbitAmplitudeRate f g h z left upper s) s := by
    refine ((FDNLS.hasDerivAt_staggerPhase ω s).fun_mul (offOrbitAmplitude_hasDerivAt f g h z left upper s)).congr_deriv ?_
    ring
  have h1 := ((hp.mul (offOrbitAmplitude_continuous f g h z left upper)).const_mul (-(I*(ω:ℂ)))).intervalIntegrable (μ := volume) 0 x
  have h2 := (hp.mul (offOrbitAmplitudeRate_continuous f g h z left upper)).intervalIntegrable (μ := volume) 0 x
  simp only [Pi.mul_apply] at h1
  change IntervalIntegrable (fun s => FDNLS.staggerPhase ω s*offOrbitAmplitudeRate f g h z left upper s) volume 0 x at h2
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul] at hi
  have hz : FDNLS.staggerPhase ω 0 = 1 := by simp [FDNLS.staggerPhase]
  rw [hz, one_mul] at hi
  exact (eq_sub_iff_add_eq.mpr hi)

/-- The differentiated oscillatory remainder has a uniform integral bound. -/
theorem offOrbitSource_remainder_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖∫ s in (0:ℝ)..|x|, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*
      offOrbitAmplitudeRate f g h z left upper s‖ ≤ ∫ s, offOrbitAmplitudeMajor f g h left upper s := by
  have hm := offOrbitAmplitudeMajor_continuous f g h left upper
  calc
    _ ≤ ∫ s in (0:ℝ)..|x|, offOrbitAmplitudeMajor f g h left upper s := by
      apply intervalIntegral.norm_integral_le_of_norm_le (abs_nonneg x) _ (hm.intervalIntegrable 0 |x|)
      filter_upwards with s hs
      rw [norm_mul, FDNLS.norm_staggerPhase, one_mul]
      have hh := offOrbitAmplitudeRate_bound f g h z left upper s
      have hs0 : 0 ≤ s := hs.1.le
      simpa only [abs_of_nonneg hs0] using hh
    _ ≤ _ := by
      rw [intervalIntegral.integral_of_le (abs_nonneg x)]
      exact setIntegral_le_integral (offOrbitAmplitudeMajor_integrable f g h left upper)
        (Eventually.of_forall (offOrbitAmplitudeMajor_nonneg f g h left upper))

/-- The source gains one complete power of frequency, uniformly on both half-lines. -/
theorem offOrbitSource_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    2*|z| *‖offOrbitSource f g h z left upper |x|‖ ≤ offOrbitAmplitudeBudget f g h left upper := by
  have hi := congrArg norm (offOrbitSource_ibp f g h z left upper |x|)
  simp only [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    offOrbitFrequency_abs] at hi
  rw [hi]
  have hb := offOrbitAmplitude_bound f g h z left upper x
  have h0 := offOrbitAmplitude_bound f g h z left upper 0
  simp only [abs_zero] at h0
  have hp : ‖FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *
      offOrbitAmplitude f g h z left upper |x|‖ = ‖offOrbitAmplitude f g h z left upper |x|‖ := by
    rw [norm_mul, FDNLS.norm_staggerPhase, one_mul]
  have htri := norm_sub_le
    (FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *offOrbitAmplitude f g h z left upper |x|)
    (offOrbitAmplitude f g h z left upper 0)
  rw [hp] at htri
  have hr := offOrbitSource_remainder_bound f g h z left upper x
  have htri2 := norm_sub_le
    (FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *offOrbitAmplitude f g h z left upper |x|-
      offOrbitAmplitude f g h z left upper 0)
    (∫ s in (0:ℝ)..|x|, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*offOrbitAmplitudeRate f g h z left upper s)
  unfold offOrbitAmplitudeBudget
  linarith

end
end GaloisForLFunctions.HTGeometry.FokasLenells
