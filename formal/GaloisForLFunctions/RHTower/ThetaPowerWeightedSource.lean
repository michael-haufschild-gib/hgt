import GaloisForLFunctions.RHTower.ThetaArithmeticTerminalCusp
import GaloisForLFunctions.RHTower.ThetaContinuousRateOrbitDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Literal power-weighted theta carriers

The measure is exactly `k(x)^(-q) dx`. Its real and complex `L²`
membership conditions are the same weighted source energy. The complete
finite-shift cusp asymptotics supply both model-energy ratios.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- The literal measure of the theta Hilbert scale. -/
def thetaPowerWeightedMeasure (q : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (thetaCuspFullSource x ^ (-q)))

/-- Real-source squared energy in the literal theta Hilbert scale. -/
def thetaPowerWeightedEnergy (q : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x ^ 2 * thetaCuspFullSource x ^ (-q)

theorem thetaPowerWeightedEnergy_nonneg (q : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    0 ≤ thetaPowerWeightedEnergy q f x :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (thetaCuspFullSource_pos_all x).le _)

theorem continuous_thetaPowerWeightedEnergy (q : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (thetaPowerWeightedEnergy q f) :=
  (hf.pow 2).mul (contDiff_thetaCuspFullSource.continuous.rpow_const
    fun x => Or.inl (thetaCuspFullSource_pos_all x).ne')

theorem continuous_finiteArithmeticThetaShift (D : Finset ℕ) (c : ℕ → ℝ) :
    Continuous (finiteArithmeticThetaShift D c) := by
  have hsource := contDiff_thetaCuspFullSource.continuous
  unfold finiteArithmeticThetaShift
  fun_prop

/-- Actual real `L²` membership is exactly weighted energy integrability. -/
theorem memLp_thetaPowerWeightedMeasure_iff (q : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (thetaPowerWeightedMeasure q) ↔ Integrable (thetaPowerWeightedEnergy q f) := by
  have hw : Measurable (fun x => ENNReal.ofReal (thetaCuspFullSource x ^ (-q))) :=
    (contDiff_thetaCuspFullSource.continuous.rpow_const
      fun x => Or.inl (thetaCuspFullSource_pos_all x).ne').measurable.ennreal_ofReal
  rw [thetaPowerWeightedMeasure, memLp_two_iff_integrable_sq hf.aestronglyMeasurable,
    integrable_withDensity_iff_integrable_smul' hw
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have heq : (fun x => (ENNReal.ofReal (thetaCuspFullSource x ^ (-q))).toReal • f x ^ 2) =
      thetaPowerWeightedEnergy q f := by
    funext x
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (thetaCuspFullSource_pos_all x).le _),
      smul_eq_mul, thetaPowerWeightedEnergy]
    ring
  rw [heq]

/-- The real source has the same membership in the complex Hilbert carrier. -/
theorem memLp_ofReal_thetaPowerWeightedMeasure_iff
    (q : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp (fun x => (f x : ℂ)) 2 (thetaPowerWeightedMeasure q) ↔
      Integrable (thetaPowerWeightedEnergy q f) := by
  have hcomplex : Continuous (fun x => (f x : ℂ)) := by
    simpa only [Function.comp_def] using Complex.continuous_ofReal.comp hf
  rw [memLp_two_iff_integrable_sq_norm hcomplex.aestronglyMeasurable]
  have hnorm : (fun x => ‖(f x : ℂ)‖ ^ 2) = fun x => f x ^ 2 := by
    funext x
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm, ← memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  exact memLp_thetaPowerWeightedMeasure_iff q hf

/-- The full double-exponential energy envelope of a negative-cusp shift. -/
def thetaShiftPowerEnvelope (q a x : ℝ) : ℝ :=
  thetaEnvelope (x - a) ^ 2 * thetaEnvelope x ^ (-q)

theorem thetaShiftPowerEnvelope_pos (q a x : ℝ) : 0 < thetaShiftPowerEnvelope q a x :=
  mul_pos (sq_pos_of_pos (thetaEnvelope_pos _)) (Real.rpow_pos_of_pos (thetaEnvelope_pos _) _)

private theorem envelope_eq_exp (x : ℝ) :
    thetaEnvelope x = Real.exp (9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
  rw [thetaEnvelope, ← Real.exp_add]
  congr 1
  ring

/-- Exact energy exponent; the threshold comes from its complete Gaussian coefficient. -/
theorem thetaShiftPowerEnvelope_eq_exp (q a x : ℝ) :
    thetaShiftPowerEnvelope q a x =
      Real.exp (9 * (2 - q) * x / 2 - 9 * a +
        Real.pi * (q - 2 * Real.exp (-2 * a)) * Real.exp (2 * x)) := by
  rw [thetaShiftPowerEnvelope, envelope_eq_exp, envelope_eq_exp,
    ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
  norm_num only [Nat.cast_ofNat]
  congr 1
  rw [show 2 * (x - a) = 2 * x + -2 * a by ring, Real.exp_add]
  ring

private theorem energy_ratio_tendsto (q a c : ℝ) (f : ℝ → ℝ)
    (hf : Tendsto (fun x => f x / thetaEnvelope (x - a)) atTop (𝓝 c)) :
    Tendsto (fun x => thetaPowerWeightedEnergy q f x / thetaShiftPowerEnvelope q a x)
      atTop (𝓝 (c ^ 2 * (4 * Real.pi ^ 2) ^ (-q))) := by
  have hpower := (Real.continuousAt_rpow_const (4 * Real.pi ^ 2) (-q)
    (Or.inl (by positivity))).tendsto.comp thetaCuspFullSource_div_envelope_tendsto
  have h := (hf.pow 2).mul hpower
  apply h.congr'
  filter_upwards with x
  simp only [Function.comp_def]
  rw [Real.div_rpow (thetaCuspFullSource_pos_all x).le (thetaEnvelope_pos x).le]
  dsimp only [thetaPowerWeightedEnergy, thetaShiftPowerEnvelope]
  field_simp [(thetaEnvelope_pos (x - a)).ne',
    (Real.rpow_pos_of_pos (thetaEnvelope_pos x) (-q)).ne']

/-- Exact negative-cusp energy ratio for every signed finite arithmetic shift polynomial. -/
theorem finiteArithmeticThetaShift_negative_energy_ratio
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) (q : ℝ) :
    Tendsto (fun x => thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c) (-x) /
      thetaShiftPowerEnvelope q (Real.log (b : ℝ)) x)
      atTop (𝓝 ((c b * (4 * Real.pi ^ 2)) ^ 2 * (4 * Real.pi ^ 2) ^ (-q))) := by
  have hshift : Tendsto (fun x : ℝ => x - Real.log (b : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-Real.log (b : ℝ)) (tendsto_id (α := ℝ))
  have h := (finiteArithmeticThetaShift_terminal_ratio D c b hb hpositive hmax).mul
    (thetaCuspFullSource_div_envelope_tendsto.comp hshift)
  have hf : Tendsto (fun x => finiteArithmeticThetaShift D c (-x) /
      thetaEnvelope (x - Real.log (b : ℝ))) atTop (𝓝 (c b * (4 * Real.pi ^ 2))) := by
    apply h.congr'
    filter_upwards with x
    simp only [Function.comp_def]
    field_simp [(thetaCuspFullSource_pos_all (x - Real.log (b : ℝ))).ne',
      (thetaEnvelope_pos (x - Real.log (b : ℝ))).ne']
  simpa only [thetaPowerWeightedEnergy, thetaCuspFullSource_neg] using
    energy_ratio_tendsto q (Real.log (b : ℝ)) (c b * (4 * Real.pi ^ 2))
      (fun x => finiteArithmeticThetaShift D c (-x)) hf

/-- The positive-cusp energy has a finite envelope ratio, including sources with no shift one. -/
theorem finiteArithmeticThetaShift_positive_energy_ratio
    (D : Finset ℕ) (c : ℕ → ℝ) (hpositive : ∀ d ∈ D, 0 < d) (q : ℝ) :
    Tendsto (fun x => thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c) x /
      thetaShiftPowerEnvelope q 0 x)
      atTop (𝓝 (((if 1 ∈ D then c 1 else 0) * (4 * Real.pi ^ 2)) ^ 2 *
        (4 * Real.pi ^ 2) ^ (-q))) := by
  classical
  have h := (finiteArithmeticThetaShift_positive_ratio D c hpositive).mul
    thetaCuspFullSource_div_envelope_tendsto
  have hf : Tendsto (fun x => finiteArithmeticThetaShift D c x / thetaEnvelope (x - 0))
      atTop (𝓝 ((if 1 ∈ D then c 1 else 0) * (4 * Real.pi ^ 2))) := by
    apply h.congr'
    filter_upwards with x
    rw [sub_zero]
    field_simp [(thetaCuspFullSource_pos_all x).ne', (thetaEnvelope_pos x).ne']
  exact energy_ratio_tendsto q 0 ((if 1 ∈ D then c 1 else 0) * (4 * Real.pi ^ 2))
    (finiteArithmeticThetaShift D c) hf

end

end RHTower
