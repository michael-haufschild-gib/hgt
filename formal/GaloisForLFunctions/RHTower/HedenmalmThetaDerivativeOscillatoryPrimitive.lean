import GaloisForLFunctions.RHTower.HedenmalmThetaDerivativeHistoryFourier

/-!
# Exact derivative expansion of the canonical theta divisor mode

The literal ordinary derivative primitives admit every complex Fourier tilt.
At an actual Xi zero each primitive can be represented by either tail.
Repeated integration by parts separates a finite derivative history from
the exact inverse-frequency oscillatory remainder, without changing the
canonical source-mode normalization.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.HedenmalmThetaSource
open HedenmalmQuantile HedenmalmPrimeTranslation

def thetaDerivativeOscillatoryIntegrand (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  thetaSourceDerivativeFunction n x * sourceChar z x

def thetaDerivativeOscillatoryPrimitive (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * z) * (x : ℂ)) *
    ∫ y in Iic x, thetaDerivativeOscillatoryIntegrand n z y

theorem integrable_thetaDerivativeOscillatoryIntegrand (n : ℕ) (z : ℂ) :
    Integrable (thetaDerivativeOscillatoryIntegrand n z) :=
  integrable_thetaSourceDerivativeFourierIntegrand z n

theorem continuous_thetaDerivativeOscillatoryIntegrand (n : ℕ) (z : ℂ) :
    Continuous (thetaDerivativeOscillatoryIntegrand n z) :=
  (continuous_thetaSourceDerivativeFunction n).mul (continuous_sourceChar z)

theorem thetaDerivativeOscillatoryIntegral (n : ℕ) (z : ℂ) :
    (∫ x, thetaDerivativeOscillatoryIntegrand n z x) =
      (-Complex.I * z) ^ n * XiC z :=
  thetaSourceDerivativeFourierIntegral z n

theorem thetaDerivativeOscillatoryPrimitive_tail (n : ℕ) {z : ℂ}
    (hz : XiC z = 0) (x : ℝ) :
    thetaDerivativeOscillatoryPrimitive n z x =
      -Complex.exp (-(Complex.I * z) * (x : ℂ)) *
        ∫ y in Ioi x, thetaDerivativeOscillatoryIntegrand n z y := by
  have h := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi
    (integrable_thetaDerivativeOscillatoryIntegrand n z) x
  rw [thetaDerivativeOscillatoryIntegral, hz, mul_zero] at h
  unfold thetaDerivativeOscillatoryPrimitive
  linear_combination Complex.exp (-(Complex.I * z) * (x : ℂ)) * h

theorem thetaDerivativeOscillatoryIntegrand_tendsto_atBot (n : ℕ) (z : ℂ) :
    Tendsto (thetaDerivativeOscillatoryIntegrand n z) atBot (𝓝 0) := by
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt |z.im|
  let c : ℝ := ((q + 1 : ℕ) : ℝ) - |z.im|
  have hc : 0 < c := by dsimp [c]; push_cast; linarith
  have hphase (x : ℝ) : -z.im * x ≤ |z.im| * |x| := by
    have h := neg_abs_le (z.im * x)
    rw [abs_mul] at h
    nlinarith
  have hb : ∀ᶠ x : ℝ in atBot,
      ‖thetaDerivativeOscillatoryIntegrand n z x‖ ≤
        finitePrimeThetaCuspWeightedDerivativeConstant n q * Real.exp (c * x) := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    calc
      ‖thetaDerivativeOscillatoryIntegrand n z x‖ =
          |iteratedDeriv n thetaCuspFullSource x| * Real.exp (-z.im * x) := by
        simp only [thetaDerivativeOscillatoryIntegrand, thetaSourceDerivativeFunction,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sourceChar]
      _ ≤ Real.exp (|z.im| * |x|) * |iteratedDeriv n thetaCuspFullSource x| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hphase x)) (abs_nonneg _)
      _ ≤ finitePrimeThetaCuspWeightedDerivativeConstant n q * Real.exp (c * x) := by
        simpa only [c, abs_of_nonpos hx, mul_neg, neg_mul, neg_neg] using
          exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource_le n q |z.im| x
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hb
    (by simpa using
      ((Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atBot hc tendsto_id)).const_mul
        (finitePrimeThetaCuspWeightedDerivativeConstant n q)))

theorem thetaDerivativeOscillatoryPrimitive_succ (n : ℕ) (z : ℂ) (x : ℝ) :
    thetaDerivativeOscillatoryPrimitive (n + 1) z x =
      thetaSourceDerivativeFunction n x -
        (Complex.I * z) * thetaDerivativeOscillatoryPrimitive n z x := by
  have hd (y : ℝ) : HasDerivAt (thetaDerivativeOscillatoryIntegrand n z)
      (thetaDerivativeOscillatoryIntegrand (n + 1) z y +
        (Complex.I * z) * thetaDerivativeOscillatoryIntegrand n z y) y := by
    have hp : HasDerivAt (sourceChar z)
        ((Complex.I * z) * sourceChar z y) y := by
      change HasDerivAt (fun t : ℝ => Complex.exp ((Complex.I * z) * (t : ℂ))) _ y
      refine ((hasDerivAt_id y).ofReal_comp.const_mul (Complex.I * z)).cexp.congr_deriv ?_
      simp only [id_eq, Complex.ofReal_one, mul_one, sourceChar]
      ring
    refine ((hasDerivAt_thetaSourceDerivativeFunction n y).mul hp).congr_deriv ?_
    dsimp only [thetaDerivativeOscillatoryIntegrand]
    ring
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (fun y _ => hd y)
    ((integrable_thetaDerivativeOscillatoryIntegrand (n + 1) z).add
      ((integrable_thetaDerivativeOscillatoryIntegrand n z).const_mul (Complex.I * z))).integrableOn
    (thetaDerivativeOscillatoryIntegrand_tendsto_atBot n z)
  rw [integral_add (integrable_thetaDerivativeOscillatoryIntegrand (n + 1) z).integrableOn
      ((integrable_thetaDerivativeOscillatoryIntegrand n z).const_mul (Complex.I * z)).integrableOn,
    integral_const_mul, sub_zero] at h
  have hphase : Complex.exp (-(Complex.I * z) * (x : ℂ)) * sourceChar z x = 1 := by
    rw [sourceChar, ← Complex.exp_add]
    rw [show -(Complex.I * z) * (x : ℂ) + Complex.I * z * (x : ℂ) = 0 by ring,
      Complex.exp_zero]
  dsimp only [thetaDerivativeOscillatoryPrimitive, thetaDerivativeOscillatoryIntegrand]
  simp only [thetaDerivativeOscillatoryIntegrand] at h
  linear_combination Complex.exp (-(Complex.I * z) * (x : ℂ)) * h +
    thetaSourceDerivativeFunction n x * hphase

theorem sourceModeF_eq_thetaDerivativeOscillatoryPrimitive_zero (z : ℂ) (x : ℝ) :
    sourceModeF thetaSource z x =
      (Complex.I * z) * thetaDerivativeOscillatoryPrimitive 0 z x := by
  simp only [sourceModeF, sourceModeU, sourceModeI, thetaDerivativeOscillatoryPrimitive,
    thetaDerivativeOscillatoryIntegrand, thetaSourceDerivativeFunction, iteratedDeriv_zero,
    thetaSource_k]
  ring

theorem continuous_thetaDerivativeOscillatoryPrimitive (n : ℕ) (z : ℂ) :
    Continuous (thetaDerivativeOscillatoryPrimitive n z) := by
  have hleft : Continuous (fun x : ℝ => ∫ y in Iic x,
      thetaDerivativeOscillatoryIntegrand n z y) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_setIntegral_Iic (continuous_thetaDerivativeOscillatoryIntegrand n z)
        (integrable_thetaDerivativeOscillatoryIntegrand n z) x).continuousAt
  exact (by fun_prop : Continuous (fun x : ℝ =>
    Complex.exp (-(Complex.I * z) * (x : ℂ)))).mul hleft

theorem thetaDerivativeOscillatoryPrimitive_reciprocal (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (x : ℝ) :
    thetaDerivativeOscillatoryPrimitive n z x =
      -(-Complex.I * z)⁻¹ * thetaSourceDerivativeFunction n x +
        (-Complex.I * z)⁻¹ * thetaDerivativeOscillatoryPrimitive (n + 1) z x := by
  have h := thetaDerivativeOscillatoryPrimitive_succ n z x
  field_simp [hz, Complex.I_ne_zero]
  linear_combination h

/-- The actual finite derivative expansion, with its exact oscillatory remainder. -/
theorem sourceModeF_derivative_expansion (A : ℕ) {z : ℂ} (hz : z ≠ 0) (x : ℝ) :
    sourceModeF thetaSource z x =
      (∑ j ∈ Finset.range (A + 1), (-Complex.I * z)⁻¹ ^ j *
        thetaSourceDerivativeFunction j x) -
      (-Complex.I * z)⁻¹ ^ A * thetaDerivativeOscillatoryPrimitive (A + 1) z x := by
  induction A with
  | zero =>
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul]
      rw [sourceModeF_eq_thetaDerivativeOscillatoryPrimitive_zero]
      linear_combination thetaDerivativeOscillatoryPrimitive_succ 0 z x
  | succ A ih =>
      rw [Finset.sum_range_succ, ih,
        thetaDerivativeOscillatoryPrimitive_reciprocal (A + 1) hz x, pow_succ]
      ring

end RHTower.HedenmalmThetaSource
