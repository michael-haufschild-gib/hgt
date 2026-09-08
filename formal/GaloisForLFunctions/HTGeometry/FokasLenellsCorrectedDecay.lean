import GaloisForLFunctions.HTGeometry.FokasLenellsDiagonalTest
import GaloisForLFunctions.HTGeometry.FokasLenellsCorrectedOrbit

/-!
# The corrected orbit gains a spectral power

The corrected equation has zero initial value. Its oscillatory source gains
one spectral power by the general Schwartz test estimate; both remaining
sources already contain an off-diagonal orbit with that gain. Gronwall
preserves the gain through the residual diagonal transport.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def correctedOffRemainder (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  -(offOrbitCoefficient f g h left upper x*offOrbitCoefficient f g h left (!upper) x)*offOrbit f g h z left upper x+
    offOrbitCoefficient f g h left upper 0*FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
      (offOrbitCoefficient f g h left upper x*offOrbit f g h z left (!upper) x)

theorem correctedOffRemainder_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (correctedOffRemainder f g h z left upper) := by
  have hp : Continuous (FDNLS.staggerPhase (offOrbitFrequency z left upper)) := by unfold FDNLS.staggerPhase; fun_prop
  exact ((((offOrbitCoefficient f g h left upper).continuous.mul (offOrbitCoefficient f g h left (!upper)).continuous).neg).mul
    (offOrbit_continuous f g h z left upper)).add
      ((continuous_const.mul hp).mul ((offOrbitCoefficient f g h left upper).continuous.mul
        (offOrbit_continuous f g h z left (!upper))))

def correctedOffMajor (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) : ℝ :=
  ‖mulS (offOrbitCoefficient f g h left upper) (offOrbitCoefficient f g h left (!upper)) x‖*
    offOrbitDecayConstant f g h left upper+
  ‖offOrbitCoefficient f g h left upper 0‖*‖offOrbitCoefficient f g h left upper x‖*
    offOrbitDecayConstant f g h left (!upper)

theorem correctedOffMajor_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) :
    0 ≤ correctedOffMajor f g h left upper x := by
  unfold correctedOffMajor
  positivity [offOrbitDecayConstant_nonneg f g h left upper,offOrbitDecayConstant_nonneg f g h left (!upper)]

theorem correctedOffMajor_continuous (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    Continuous (correctedOffMajor f g h left upper) :=
  (((mulS (offOrbitCoefficient f g h left upper) (offOrbitCoefficient f g h left (!upper))).continuous.norm).mul_const _).add
    (((offOrbitCoefficient f g h left upper).continuous.norm.const_mul _).mul_const _)

theorem correctedOffMajor_integrable (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    Integrable (correctedOffMajor f g h left upper) :=
  (((mulS (offOrbitCoefficient f g h left upper) (offOrbitCoefficient f g h left (!upper))).integrable.norm).mul_const _).add
    (((offOrbitCoefficient f g h left upper).integrable.norm.const_mul _).mul_const _)

/-- Both nonoscillatory remainder channels inherit the previously established first spectral power. -/
theorem correctedOffRemainder_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    |z| *‖correctedOffRemainder f g h z left upper |x|‖ ≤ correctedOffMajor f g h left upper |x| := by
  have h1 := offOrbit_frequency_bound f g h z left upper x
  have h2 := offOrbit_frequency_bound f g h z left (!upper) x
  unfold correctedOffRemainder
  calc
    _ ≤ |z| *(‖-(offOrbitCoefficient f g h left upper |x| *offOrbitCoefficient f g h left (!upper) |x|)*
        offOrbit f g h z left upper |x|‖+
      ‖offOrbitCoefficient f g h left upper 0*FDNLS.staggerPhase (offOrbitFrequency z left upper) |x| *
        (offOrbitCoefficient f g h left upper |x| *offOrbit f g h z left (!upper) |x|)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg z)
    _ = (‖offOrbitCoefficient f g h left upper |x|‖*‖offOrbitCoefficient f g h left (!upper) |x|‖)*
        (|z| *‖offOrbit f g h z left upper |x|‖)+
      (‖offOrbitCoefficient f g h left upper 0‖*‖offOrbitCoefficient f g h left upper |x|‖)*
        (|z| *‖offOrbit f g h z left (!upper) |x|‖) := by
      simp only [norm_mul,norm_neg,FDNLS.norm_staggerPhase,mul_one]
      ring
    _ ≤ (‖offOrbitCoefficient f g h left upper |x|‖*‖offOrbitCoefficient f g h left (!upper) |x|‖)*
        offOrbitDecayConstant f g h left upper+
      (‖offOrbitCoefficient f g h left upper 0‖*‖offOrbitCoefficient f g h left upper |x|‖)*
        offOrbitDecayConstant f g h left (!upper) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by simp only [correctedOffMajor,mulS_apply,norm_mul]

def correctedOffSource (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  diagonalTestSource f g h (correctedOffCoefficient f g h left upper) z left upper x+
    ∫ s in (0:ℝ)..x, correctedOffRemainder f g h z left upper s

def correctedOffSourceBudget (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : ℝ :=
  diagonalTestBudget f g h (correctedOffCoefficient f g h left upper) left/2+
    ∫ s, correctedOffMajor f g h left upper s

theorem correctedOffSourceBudget_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    0 ≤ correctedOffSourceBudget f g h left upper := by
  have hi : 0 ≤ ∫ s, correctedOffMajor f g h left upper s :=
    MeasureTheory.integral_nonneg (correctedOffMajor_nonneg f g h left upper)
  unfold correctedOffSourceBudget
  positivity [diagonalTestBudget_nonneg f g h (correctedOffCoefficient f g h left upper) left]

/-- A single finite constant bounds the full corrected source after multiplying by frequency. -/
theorem correctedOffSource_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    |z| *‖correctedOffSource f g h z left upper |x|‖ ≤ correctedOffSourceBudget f g h left upper := by
  have hr : |z| *‖∫ s in (0:ℝ)..|x|, correctedOffRemainder f g h z left upper s‖ ≤
      ∫ s, correctedOffMajor f g h left upper s := by
    calc
      _ ≤ |z| *(∫ s in (0:ℝ)..|x|, ‖correctedOffRemainder f g h z left upper s‖) :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm (abs_nonneg x)) (abs_nonneg z)
      _ = ∫ s in (0:ℝ)..|x|, |z| *‖correctedOffRemainder f g h z left upper s‖ := by rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ s in (0:ℝ)..|x|, correctedOffMajor f g h left upper s := by
        apply intervalIntegral.integral_mono_on (abs_nonneg x)
          (((correctedOffRemainder_continuous f g h z left upper).norm.const_mul |z|).intervalIntegrable 0 |x|)
          ((correctedOffMajor_continuous f g h left upper).intervalIntegrable 0 |x|)
        intro s hs
        simpa only [abs_of_nonneg hs.1] using correctedOffRemainder_frequency_bound f g h z left upper s
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le (abs_nonneg x)]
        exact setIntegral_le_integral (correctedOffMajor_integrable f g h left upper)
          (Eventually.of_forall (correctedOffMajor_nonneg f g h left upper))
  have hs := diagonalTestSource_frequency_bound f g h (correctedOffCoefficient f g h left upper) z left upper x
  have ht := mul_le_mul_of_nonneg_left
    (norm_add_le (diagonalTestSource f g h (correctedOffCoefficient f g h left upper) z left upper |x|)
      (∫ s in (0:ℝ)..|x|, correctedOffRemainder f g h z left upper s)) (abs_nonneg z)
  change |z| *‖_+_‖ ≤ _
  unfold correctedOffSourceBudget
  nlinarith

/-- The corrected orbit satisfies a zero-initial-value Volterra equation. -/
theorem correctedOffOrbit_integral (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    correctedOffOrbit f g h z left upper x =
      (∫ s in (0:ℝ)..x, offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s)+
        correctedOffSource f g h z left upper x := by
  have hp : Continuous (FDNLS.staggerPhase (offOrbitFrequency z left upper)) := by unfold FDNLS.staggerPhase; fun_prop
  have h1 : IntervalIntegrable (fun s => offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s) volume 0 x :=
    ((offOrbitDiagonal f g h left upper).continuous.mul (correctedOffOrbit_continuous f g h z left upper)).intervalIntegrable 0 x
  have h2 : IntervalIntegrable (fun s => FDNLS.staggerPhase (offOrbitFrequency z left upper) s*
      diagonalTestAmplitude f g h (correctedOffCoefficient f g h left upper) z left upper s) volume 0 x :=
    (hp.mul (diagonalTestAmplitude_continuous f g h (correctedOffCoefficient f g h left upper) z left upper)).intervalIntegrable 0 x
  have h3 := (correctedOffRemainder_continuous f g h z left upper).intervalIntegrable (μ := volume) 0 x
  have he : correctedOffRate f g h z left upper = fun s =>
      (offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s+
        FDNLS.staggerPhase (offOrbitFrequency z left upper) s*diagonalTestAmplitude f g h (correctedOffCoefficient f g h left upper) z left upper s)+
        correctedOffRemainder f g h z left upper s := by
    funext s
    unfold correctedOffRate correctedOffRemainder diagonalTestAmplitude
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => correctedOffOrbit_hasDerivAt f g h z left upper s)
    ((correctedOffRate_continuous f g h z left upper).intervalIntegrable 0 x)
  rw [correctedOffOrbit_initial,sub_zero,he,intervalIntegral.integral_add (h1.add h2) h3,intervalIntegral.integral_add h1 h2] at hi
  change _ = _+((∫ s in (0:ℝ)..x, FDNLS.staggerPhase (offOrbitFrequency z left upper) s*
    diagonalTestAmplitude f g h (correctedOffCoefficient f g h left upper) z left upper s)+_)
  rw [← hi]
  abel

def correctedOffDecayConstant (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : ℝ :=
  correctedOffSourceBudget f g h left upper*Real.exp (effectiveMass f g h)

theorem correctedOffDecayConstant_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    0 ≤ correctedOffDecayConstant f g h left upper :=
  mul_nonneg (correctedOffSourceBudget_nonneg f g h left upper) (Real.exp_pos _).le

/-- Diagonal transport preserves the corrected source's spectral-power gain. -/
theorem correctedOffOrbit_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    |z| *‖correctedOffOrbit f g h z left upper |x|‖ ≤ correctedOffDecayConstant f g h left upper := by
  have hS := (correctedOffOrbit_continuous f g h z left upper).norm.const_mul |z|
  have hk := (offOrbitDiagonal f g h left upper).continuous.norm
  apply le_mul_exp_of_le_add_integral_of_mass_le (A := 0) (B := |x|)
    (S := fun s => |z| *‖correctedOffOrbit f g h z left upper s‖)
    (k := fun s => ‖offOrbitDiagonal f g h left upper s‖)
    (abs_nonneg x) hS.continuousOn hk.continuousOn (fun _ _ => norm_nonneg _)
    (correctedOffSourceBudget_nonneg f g h left upper)
  · intro y hy
    have hs := correctedOffSource_frequency_bound f g h z left upper y
    rw [abs_of_nonneg hy.1] at hs
    have hi : ‖∫ s in (0:ℝ)..y, offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s‖ ≤
        ∫ s in (0:ℝ)..y, ‖offOrbitDiagonal f g h left upper s‖*‖correctedOffOrbit f g h z left upper s‖ := by
      simpa only [norm_mul] using intervalIntegral.norm_integral_le_integral_norm
        (f := fun s => offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s) hy.1
    calc
      _ = |z| *‖(∫ s in (0:ℝ)..y, offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s)+
          correctedOffSource f g h z left upper y‖ := by rw [correctedOffOrbit_integral]
      _ ≤ |z| *(‖∫ s in (0:ℝ)..y, offOrbitDiagonal f g h left upper s*correctedOffOrbit f g h z left upper s‖+
          ‖correctedOffSource f g h z left upper y‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg z)
      _ ≤ |z| *(∫ s in (0:ℝ)..y, ‖offOrbitDiagonal f g h left upper s‖*‖correctedOffOrbit f g h z left upper s‖)+
          correctedOffSourceBudget f g h left upper := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left hi (abs_nonneg z)) hs
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul,add_comm]
        congr 1
        apply intervalIntegral.integral_congr
        intro s _
        ring
  · intro y hy
    calc
      (∫ s in (0:ℝ)..y, ‖offOrbitDiagonal f g h left upper s‖) ≤
          ∫ s in (0:ℝ)..y, orientedEffectiveDensity f g h left s :=
        intervalIntegral.integral_mono_on hy.1 (hk.intervalIntegrable 0 y)
          ((orientedEffectiveDensity_continuous f g h left).intervalIntegrable 0 y)
          (fun s _ => offOrbitDiagonal_le_density f g h left upper s)
      _ ≤ effectiveMass f g h := by
        rw [intervalIntegral.integral_of_le hy.1,← orientedEffectiveDensity_integral f g h left]
        exact setIntegral_le_integral (orientedEffectiveDensity_integrable f g h left)
          (Eventually.of_forall (orientedEffectiveDensity_nonneg f g h left))
  · exact ⟨abs_nonneg x,le_rfl⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
