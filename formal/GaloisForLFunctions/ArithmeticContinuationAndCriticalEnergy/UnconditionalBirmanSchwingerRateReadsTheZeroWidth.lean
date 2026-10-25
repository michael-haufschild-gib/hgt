import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq
import GaloisForLFunctions.RHTower.XiGlobalPacketDensity
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanLogWeightEquivalence
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFiniteNegativeBlock
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensatedWidthFloorAndGroundEnergyRate
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The Form-Domain Birman–Schwinger Rate Unconditionally Reads the Zero Width

On physical `L²(-a, a)`, the uncompensated negative zero-pair energy `E_-(u)` is bounded only when
off-line zeros do not cluster locally in height (`exists_uncompensated_pairedMinusEnergy_bound_iff`).
Passing from physical `L²(-a, a)` to the intrinsic Archimedean Hilbert form domain
`CCMArchimedeanFormDomain a` supplies the logarithmic frequency weight `1 + log⁺ |ξ|` equivalent to
Connes–Consani's digamma weight `ccmArchimedeanFormWeight`, which absorbs the global `O(log(2+|T|))`
divisor packet density unconditionally without any non-clustering hypothesis.

## Main results

1. **Exponential-tilt stability in the CCM form norm (`norm_sq_expTiltSource_toCCMFormVector_le`).**
   Via the exact Gamma–Lévy jump representation `lintegral_archSymbol_mul_normSq_fourier`, tilting a
   smooth interior source `u ∈ C_c^∞(-a, a)` by `e^{ηx}` (`|η| ≤ Λ`, `Λa ≤ B`) multiplies its squared
   `CCMArchimedeanFormDomain a` norm by at most `e^{2B} (2 + 16 Λ ∫_{0}^∞ e^{-h/4} dh)`.

2. **Unconditional rotated-disk sampling and two-sided restricted-Weil form bound
   (`exists_unconditional_pairedEnergy_and_birmanSchwinger_bounds`).**
   Combining planar subharmonic mean-square sampling on disks of radius `r = 1 / max(a, 1)` around
   the rotated spectral points `i(-z_q)` and `i(-z̄_q)` with the global logarithmic packet ceiling
   `exists_xiUnitHeightPacket_global_log_bound` and `suzukiLogWeight_le_ccmArchimedeanComparison`
   yields a single universal constant `K > 0` such that at every aperture `a > 0`:
   - `E_+(u) ≤ K max(a, 1)² e^{2 σ_ζ a} ‖u‖_{Form}²` and
     `E_-(u) ≤ K max(a, 1)² e^{2 σ_ζ a} ‖u‖_{Form}²` for every smooth interior source `u`, where
     `σ_ζ = zetaZeroWidth`;
   - `|Q_a(v)| ≤ K max(a, 1)² e^{2 σ_ζ a} ‖v‖_{Form}²` for every `v : CCMArchimedeanFormDomain a`;
   - the compact self-adjoint zero-energy Birman–Schwinger operator
     `ccmRestrictedWeilFormBirmanSchwinger a 0` satisfies the operator-norm ceiling
     `‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ ≤ 1 + K max(a, 1)² e^{2 σ_ζ a}`.

3. **Unconditional equality of the form-domain, polar form-domain, and Birman–Schwinger norm rates
   with `zetaZeroWidth` (`formGroundEnergyRate_eq_zetaZeroWidth`,
   `polarFormGroundEnergyRate_eq_zetaZeroWidth`, `birmanSchwingerNormRate_eq_zetaZeroWidth`).**
   Conversely, the unmodulated polar-free difference family `twoBump (scaledBumpPolarFree w 0) v (-1)`
   has `CCMArchimedeanFormDomain` norm bounded uniformly in the lag `v` (`≤ 4 ‖u_0‖_{Form}²`), so any
   exponential floor `-(C e^{2σa}) ‖v‖_{Form}² ≤ Q_a(v)` on polar-constrained vectors forces
   `zetaZeroWidth ≤ σ`. Thus all three exponential growth rates equal `zetaZeroWidth` unconditionally,
   and `RiemannHypothesis` holds if and only if the zero-energy Birman–Schwinger operator norm (or
   lower form floor) grows subexponentially in the aperture.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry RHTower
open Zeta23
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

/-! ## 1. Elementary Gamma–Lévy kernel majorant and bounded-exponent Lipschitz estimate -/

/-- Finite tail integral `∫_{0}^∞ e^{-h/4} dh` majorizing the truncated Gamma–Lévy jump moment. -/
private def expQuarterTail : ℝ :=
  ∫ h : ℝ in Ioi 0, Real.exp (-(1 / 4) * h)

private theorem integrableOn_expQuarter :
    IntegrableOn (fun h : ℝ => Real.exp (-(1 / 4) * h)) (Ioi 0) := by
  simpa only [neg_mul] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1 / 4) (by norm_num)

private theorem expQuarterTail_nonneg : 0 ≤ expQuarterTail :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le

/-- Elementary global bound `ω(h) min(Λh, 2)² ≤ 8 Λ e^{-h/4}` on `(0, ∞)` for `Λ ≥ 0`. -/
private theorem archLevyDensity_mul_min_sq_le {Λ h : ℝ} (hΛ : 0 ≤ Λ) (hh : 0 < h) :
    archLevyDensity h * min (Λ * h) 2 ^ 2 ≤ 8 * Λ * Real.exp (-(1 / 4) * h) := by
  have hmin_nn : 0 ≤ min (Λ * h) 2 := le_min (mul_nonneg hΛ hh.le) (by norm_num)
  have hmin_sq : min (Λ * h) 2 ^ 2 ≤ 2 * (Λ * h) := by
    rw [sq]
    exact mul_le_mul (min_le_right _ _) (min_le_left _ _) hmin_nn (by norm_num)
  have h1_sub_pos : 0 < 1 - Real.exp (-2 * h) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hexp_prod : (1 + 2 * h) * Real.exp (-2 * h) ≤ 1 := by
    have hle := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * h)) (Real.exp_pos (-2 * h)).le
    have hcancel : Real.exp (2 * h) * Real.exp (-2 * h) = 1 := by
      rw [← Real.exp_add, show 2 * h + -2 * h = 0 by ring, Real.exp_zero]
    linarith
  have hquot : 2 * h / (1 - Real.exp (-2 * h)) ≤ 1 + 2 * h := by
    rw [div_le_iff₀ h1_sub_pos]
    nlinarith
  have hlin_exp : 1 + 2 * h ≤ 8 * Real.exp (h / 4) := by
    have h4 := Real.add_one_le_exp (h / 4)
    linarith
  calc archLevyDensity h * min (Λ * h) 2 ^ 2
      ≤ archLevyDensity h * (2 * (Λ * h)) :=
        mul_le_mul_of_nonneg_left hmin_sq (archLevyDensity_pos hh).le
    _ = Λ * Real.exp (-h / 2) * (2 * h / (1 - Real.exp (-2 * h))) := by
        unfold archLevyDensity; ring
    _ ≤ Λ * Real.exp (-h / 2) * (1 + 2 * h) :=
        mul_le_mul_of_nonneg_left hquot (mul_nonneg hΛ (Real.exp_pos _).le)
    _ ≤ Λ * Real.exp (-h / 2) * (8 * Real.exp (h / 4)) :=
        mul_le_mul_of_nonneg_left hlin_exp (mul_nonneg hΛ (Real.exp_pos _).le)
    _ = 8 * Λ * (Real.exp (-h / 2) * Real.exp (h / 4)) := by ring
    _ = 8 * Λ * Real.exp (-(1 / 4) * h) := by
        rw [← Real.exp_add, show -h / 2 + h / 4 = -(1 / 4) * h by ring]

private theorem exp_sub_exp_le_of_le {q p B : ℝ} (hq : q ≤ p) (hp : p ≤ B) :
    Real.exp p - Real.exp q ≤ Real.exp B * min (p - q) 2 := by
  have h1_sub_le_d : 1 - Real.exp (-(p - q)) ≤ p - q := by
    have h := Real.add_one_le_exp (-(p - q))
    linarith
  have h1_sub_le_two : 1 - Real.exp (-(p - q)) ≤ 2 := by
    linarith [Real.exp_pos (-(p - q))]
  have h1_sub_nn : 0 ≤ 1 - Real.exp (-(p - q)) := by
    have hle1 : Real.exp (-(p - q)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hmin : 1 - Real.exp (-(p - q)) ≤ min (p - q) 2 :=
    le_min h1_sub_le_d h1_sub_le_two
  have hfac : Real.exp p - Real.exp q = Real.exp p * (1 - Real.exp (-(p - q))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [hfac]
  exact mul_le_mul (Real.exp_le_exp.mpr hp) hmin h1_sub_nn (Real.exp_pos B).le

/-- Calculus-free bounded-exponent Lipschitz estimate `|e^p - e^q| ≤ e^B min(|p - q|, 2)`. -/
private theorem abs_exp_sub_exp_le {p q B : ℝ} (hp : p ≤ B) (hq : q ≤ B) :
    |Real.exp p - Real.exp q| ≤ Real.exp B * min |p - q| 2 := by
  rcases le_total q p with hqp | hpq
  · have hnn : 0 ≤ Real.exp p - Real.exp q := sub_nonneg.mpr (Real.exp_le_exp.mpr hqp)
    rw [abs_of_nonneg hnn, abs_of_nonneg (sub_nonneg.mpr hqp)]
    exact exp_sub_exp_le_of_le hqp hp
  · have hnn : 0 ≤ Real.exp q - Real.exp p := sub_nonneg.mpr (Real.exp_le_exp.mpr hpq)
    rw [abs_sub_comm, abs_of_nonneg hnn, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hpq)]
    exact exp_sub_exp_le_of_le hpq hq

/-! ## 2. Exponential tilt of smooth interior sources in the CCM form domain -/

/-- Exponentially tilted smooth interior source `x ↦ u(x) e^{ηx}` on `(-a, a)`. -/
def expTiltSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (η : ℝ) :
    CCMComplexSmoothInteriorSource a where
  toFun x := u x * (Real.exp (η * x) : ℂ)
  smooth := u.smooth.mul (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))
  hasCompactSupport := u.hasCompactSupport.mul_right
  tsupport_subset := (tsupport_mul_subset_left (f := (u : ℝ → ℂ))
    (g := fun x : ℝ => (Real.exp (η * x) : ℂ))).trans u.tsupport_subset

@[simp]
theorem expTiltSource_apply {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (η x : ℝ) :
    expTiltSource u η x = u x * (Real.exp (η * x) : ℂ) := rfl

private theorem smoothSource_memLp_two {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    MemLp (u : ℝ → ℂ) 2 :=
  u.continuous.memLp_of_hasCompactSupport u.hasCompactSupport

private theorem smoothSource_norm_sq_integrable {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Integrable (fun x : ℝ => ‖u x‖ ^ 2) :=
  (smoothSource_memLp_two u).integrable_norm_pow (by norm_num)

/-- Exact Fourier-weight integral formula for the squared CCM form-domain norm of a smooth source. -/
theorem norm_sq_toCCMFormVector_eq_integral {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ‖u.toCCMFormVector‖ ^ 2 =
      ∫ ξ : ℝ, ccmArchimedeanFormWeight ξ * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 := by
  change ‖(u.toCCMFormVector).1‖ ^ 2 = _
  rw [norm_sq_ccmArchimedeanFourierL2]
  refine integral_congr_ae ?_
  filter_upwards [u.toCCMFormVector_fourier_coeFn] with ξ hξ
  rw [hξ]
  rfl

/-- Integrability of the CCM Fourier-weight energy of a smooth interior source. -/
theorem integrable_ccmFormWeight_mul_norm_sq_fourier {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2) := by
  have hfint : Integrable (fun ξ : ℝ => ‖((u.toCCMFormVector).1 : ℝ → ℂ) ξ‖ ^ 2)
      ccmArchimedeanFormMeasure :=
    (MeasureTheory.Lp.memLp (u.toCCMFormVector).1).integrable_norm_pow (by norm_num)
  have hw : Integrable
      (fun ξ : ℝ => Real.toNNReal (ccmArchimedeanFormWeight ξ) •
        ‖((u.toCCMFormVector).1 : ℝ → ℂ) ξ‖ ^ 2) volume :=
    (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp hfint
  refine hw.congr ?_
  filter_upwards [u.toCCMFormVector_fourier_coeFn] with ξ hξ
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal, hξ]
  rfl

private def smoothGammaExcess {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (ξ : ℝ) : ℝ :=
  2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2

private theorem smoothGammaExcess_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (ξ : ℝ) :
    0 ≤ smoothGammaExcess u ξ :=
  mul_nonneg (mul_nonneg (by norm_num)
    (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _)

private theorem ccmFormWeight_mul_fourier_eq_add_excess {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (ξ : ℝ) :
    ccmArchimedeanFormWeight ξ * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 =
      ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 + smoothGammaExcess u ξ := by
  have heven : gammaHardyPhaseRate (2 * Real.pi * |ξ|) =
      gammaHardyPhaseRate (2 * Real.pi * ξ) := by
    by_cases hξ : 0 ≤ ξ
    · rw [abs_of_nonneg hξ]
    · rw [abs_of_neg (lt_of_not_ge hξ), show 2 * Real.pi * (-ξ) = -(2 * Real.pi * ξ) by ring,
        gammaHardyPhaseRate_neg]
  unfold ccmArchimedeanFormWeight smoothGammaExcess
  rw [heven]
  ring

private theorem integrable_smoothGammaExcess {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Integrable (smoothGammaExcess u) := by
  have hf := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
    u.integrable (smoothSource_memLp_two u)
  have htot := integrable_ccmFormWeight_mul_norm_sq_fourier u
  exact (htot.sub hf).congr (Eventually.of_forall fun ξ => by
    rw [Pi.sub_apply, ccmFormWeight_mul_fourier_eq_add_excess]; ring)

private theorem norm_sq_toCCMFormVector_eq_mass_add_excess {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ‖u.toCCMFormVector‖ ^ 2 =
      (∫ x : ℝ, ‖u x‖ ^ 2) + ∫ ξ : ℝ, smoothGammaExcess u ξ := by
  have hf := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
    u.integrable (smoothSource_memLp_two u)
  rw [norm_sq_toCCMFormVector_eq_integral]
  simp_rw [ccmFormWeight_mul_fourier_eq_add_excess]
  rw [integral_add hf (integrable_smoothGammaExcess u),
    GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq u.integrable (smoothSource_memLp_two u)]

private theorem ofReal_integral_smoothGammaExcess_eq_lintegral {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ENNReal.ofReal (∫ ξ : ℝ, smoothGammaExcess u ξ) =
      ∫⁻ h : ℝ in Ioi 0, ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) := by
  have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_smoothGammaExcess u)
    (Eventually.of_forall (smoothGammaExcess_nonneg u))
  rw [h1]
  exact lintegral_archSymbol_mul_normSq_fourier u.integrable (smoothSource_memLp_two u)

private theorem pointwise_expTilt_diff_sq_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {η Λ B h : ℝ}
    (hη : |η| ≤ Λ) (hΛ : 0 ≤ Λ) (hB : Λ * a.1 ≤ B) (hh : 0 < h) (x : ℝ) :
    ‖expTiltSource u η x - expTiltSource u η (x + h)‖ ^ 2 ≤
      2 * Real.exp (2 * B) * ‖u x - u (x + h)‖ ^ 2 +
        2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2 * ‖u (x + h)‖ ^ 2 := by
  have hexp2B : Real.exp B ^ 2 = Real.exp (2 * B) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsupp_exp : ∀ z : ℝ, u z ≠ 0 → η * z ≤ B := fun z hz => by
    have hmem := u.support_subset hz
    have hz_abs : |z| ≤ a.1 := abs_le.mpr ⟨hmem.1.le, hmem.2.le⟩
    calc η * z ≤ |η * z| := le_abs_self _
      _ = |η| * |z| := abs_mul η z
      _ ≤ Λ * a.1 := mul_le_mul hη hz_abs (abs_nonneg z) hΛ
      _ ≤ B := hB
  by_cases hux : u x = 0
  · by_cases huxh : u (x + h) = 0
    · simp only [expTiltSource_apply, hux, huxh, zero_mul, sub_self, norm_zero]
      rw [zero_pow two_ne_zero]
      positivity
    · have hq : η * (x + h) ≤ B := hsupp_exp (x + h) huxh
      have hterm : ‖expTiltSource u η x - expTiltSource u η (x + h)‖ ≤
          Real.exp B * ‖u x - u (x + h)‖ := by
        simp only [expTiltSource_apply, hux, zero_mul, zero_sub, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hq) (norm_nonneg _)
      have hsq : ‖expTiltSource u η x - expTiltSource u η (x + h)‖ ^ 2 ≤
          Real.exp (2 * B) * ‖u x - u (x + h)‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hterm 2
        rwa [mul_pow, hexp2B] at this
      have hmin_nn : 0 ≤ 2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2 * ‖u (x + h)‖ ^ 2 := by
        positivity
      have hexp_nn : 0 ≤ Real.exp (2 * B) * ‖u x - u (x + h)‖ ^ 2 := by positivity
      linarith
  · by_cases huxh : u (x + h) = 0
    · have hp : η * x ≤ B := hsupp_exp x hux
      have hterm : ‖expTiltSource u η x - expTiltSource u η (x + h)‖ ≤
          Real.exp B * ‖u x - u (x + h)‖ := by
        simp only [expTiltSource_apply, huxh, zero_mul, sub_zero, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) (norm_nonneg _)
      have hsq : ‖expTiltSource u η x - expTiltSource u η (x + h)‖ ^ 2 ≤
          Real.exp (2 * B) * ‖u x - u (x + h)‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hterm 2
        rwa [mul_pow, hexp2B] at this
      have hmin_nn : 0 ≤ 2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2 * ‖u (x + h)‖ ^ 2 := by
        positivity
      have hexp_nn : 0 ≤ Real.exp (2 * B) * ‖u x - u (x + h)‖ ^ 2 := by positivity
      linarith
    · have hp : η * x ≤ B := hsupp_exp x hux
      have hq : η * (x + h) ≤ B := hsupp_exp (x + h) huxh
      have hsplit : expTiltSource u η x - expTiltSource u η (x + h) =
          (u x - u (x + h)) * (Real.exp (η * x) : ℂ) +
            u (x + h) * ((Real.exp (η * x) - Real.exp (η * (x + h)) : ℝ) : ℂ) := by
        simp only [expTiltSource_apply]
        push_cast
        ring
      have h1 : ‖(u x - u (x + h)) * (Real.exp (η * x) : ℂ)‖ ≤
          Real.exp B * ‖u x - u (x + h)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) (norm_nonneg _)
      have hpq_diff : |η * x - η * (x + h)| ≤ Λ * h := by
        rw [show η * x - η * (x + h) = -(η * h) by ring, abs_neg, abs_mul, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_right hη hh.le
      have hmin_mono : min |η * x - η * (x + h)| 2 ≤ min (Λ * h) 2 :=
        min_le_min_right 2 hpq_diff
      have h2 : ‖u (x + h) * ((Real.exp (η * x) - Real.exp (η * (x + h)) : ℝ) : ℂ)‖ ≤
          Real.exp B * min (Λ * h) 2 * ‖u (x + h)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        refine (mul_le_mul_of_nonneg_right (abs_exp_sub_exp_le hp hq) (norm_nonneg _)).trans ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmin_mono (Real.exp_pos B).le) (norm_nonneg _)
      have htri : ‖expTiltSource u η x - expTiltSource u η (x + h)‖ ≤
          Real.exp B * ‖u x - u (x + h)‖ + Real.exp B * min (Λ * h) 2 * ‖u (x + h)‖ := by
        rw [hsplit]
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      have hsq1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have h2ab : (Real.exp B * ‖u x - u (x + h)‖ +
          Real.exp B * min (Λ * h) 2 * ‖u (x + h)‖) ^ 2 ≤
          2 * (Real.exp B * ‖u x - u (x + h)‖) ^ 2 +
            2 * (Real.exp B * min (Λ * h) 2 * ‖u (x + h)‖) ^ 2 := by
        nlinarith [sq_nonneg (Real.exp B * ‖u x - u (x + h)‖ -
          Real.exp B * min (Λ * h) 2 * ‖u (x + h)‖)]
      refine hsq1.trans (h2ab.trans_eq ?_)
      rw [mul_pow, mul_pow, mul_pow, hexp2B]
      ring

private theorem integrable_diff_norm_sq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    Integrable (fun x : ℝ => ‖u x - u (x + h)‖ ^ 2) := by
  have hu2 := smoothSource_norm_sq_integrable u
  have huh2 := hu2.comp_add_right h
  refine ((hu2.const_mul 2).add (huh2.const_mul 2)).mono'
    (((u.continuous.sub (u.continuous.comp (continuous_id.add continuous_const))).norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards [] with x
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have htri : ‖u x - u (x + h)‖ ≤ ‖u x‖ + ‖u (x + h)‖ := norm_sub_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [sq_nonneg (‖u x‖ - ‖u (x + h)‖)]

/-- **Exponential-tilt stability in the CCM form norm.** Tilting `u ∈ C_c^∞(-a, a)` by `e^{ηx}`
(`|η| ≤ Λ`, `Λa ≤ B`) multiplies `‖u.toCCMFormVector‖²` by at most
`e^{2B} (2 + 16 Λ expQuarterTail)`. -/
theorem norm_sq_expTiltSource_toCCMFormVector_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {η Λ B : ℝ}
    (hη : |η| ≤ Λ) (hΛ : 0 ≤ Λ) (hB : Λ * a.1 ≤ B) :
    ‖(expTiltSource u η).toCCMFormVector‖ ^ 2 ≤
      Real.exp (2 * B) * (2 + 16 * Λ * expQuarterTail) * ‖u.toCCMFormVector‖ ^ 2 := by
  let g := expTiltSource u η
  have hexp2B : Real.exp B ^ 2 = Real.exp (2 * B) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hM_nn : 0 ≤ ∫ x : ℝ, ‖u x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hE_nn : 0 ≤ ∫ ξ : ℝ, smoothGammaExcess u ξ :=
    integral_nonneg (smoothGammaExcess_nonneg u)
  have hmass_le : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ Real.exp (2 * B) * ∫ x : ℝ, ‖u x‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (smoothSource_norm_sq_integrable g)
      ((smoothSource_norm_sq_integrable u).const_mul _) fun x => ?_
    by_cases hux : u x = 0
    · simp only [g, expTiltSource_apply, hux, zero_mul, norm_zero]
      rw [zero_pow two_ne_zero]
      positivity
    · have hmem := u.support_subset hux
      have hx_abs : |x| ≤ a.1 := abs_le.mpr ⟨hmem.1.le, hmem.2.le⟩
      have hp : η * x ≤ B :=
        (le_abs_self _).trans ((abs_mul η x).le.trans
          ((mul_le_mul hη hx_abs (abs_nonneg x) hΛ).trans hB))
      have h1 : ‖g x‖ ≤ Real.exp B * ‖u x‖ := by
        simp only [g, expTiltSource_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) (norm_nonneg _)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rwa [mul_pow, hexp2B] at hsq
  have hexcess_le : (∫ ξ : ℝ, smoothGammaExcess g ξ) ≤
      2 * Real.exp (2 * B) * (∫ ξ : ℝ, smoothGammaExcess u ξ) +
        16 * Λ * expQuarterTail * Real.exp (2 * B) * ∫ x : ℝ, ‖u x‖ ^ 2 := by
    have hQ_nn := expQuarterTail_nonneg
    have hrhs_nn : 0 ≤ 2 * Real.exp (2 * B) * (∫ ξ : ℝ, smoothGammaExcess u ξ) +
        16 * Λ * expQuarterTail * Real.exp (2 * B) * ∫ x : ℝ, ‖u x‖ ^ 2 := by
      positivity
    refine (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp ?_
    rw [ofReal_integral_smoothGammaExcess_eq_lintegral g]
    let C_exp : ℝ := 16 * Λ * Real.exp (2 * B) * ∫ x : ℝ, ‖u x‖ ^ 2
    have hC_exp_nn : 0 ≤ C_exp := by dsimp [C_exp]; positivity
    have hpt : ∀ h ∈ Ioi (0 : ℝ),
        ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖g x - g (x + h)‖ ^ 2) ≤
          ENNReal.ofReal (2 * Real.exp (2 * B)) *
              ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) +
            ENNReal.ofReal (C_exp * Real.exp (-(1 / 4) * h)) := by
      intro h hh
      have hh0 : 0 < h := hh
      have hint_step : (∫ x : ℝ, ‖g x - g (x + h)‖ ^ 2) ≤
          2 * Real.exp (2 * B) * (∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) +
            2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2 * ∫ x : ℝ, ‖u x‖ ^ 2 := by
        have h1 := integrable_diff_norm_sq u h
        have h2 := (smoothSource_norm_sq_integrable u).comp_add_right h
        have hmono := integral_mono (integrable_diff_norm_sq g h)
          ((h1.const_mul (2 * Real.exp (2 * B))).add
            (h2.const_mul (2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2)))
          (pointwise_expTilt_diff_sq_le u hη hΛ hB hh0)
        simp only [Pi.add_apply] at hmono
        rw [integral_add (h1.const_mul _) (h2.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_add_right_eq_self (fun x : ℝ => ‖u x‖ ^ 2) h] at hmono
        exact hmono
      have hmul_levy := mul_le_mul_of_nonneg_left hint_step (archLevyDensity_pos hh0).le
      have hlevy_min := archLevyDensity_mul_min_sq_le hΛ hh0
      have hsecond : archLevyDensity h *
          (2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2 * ∫ x : ℝ, ‖u x‖ ^ 2) ≤
          C_exp * Real.exp (-(1 / 4) * h) := by
        calc archLevyDensity h *
              (2 * Real.exp (2 * B) * min (Λ * h) 2 ^ 2 * ∫ x : ℝ, ‖u x‖ ^ 2)
            = 2 * Real.exp (2 * B) * (∫ x : ℝ, ‖u x‖ ^ 2) *
                (archLevyDensity h * min (Λ * h) 2 ^ 2) := by ring
          _ ≤ 2 * Real.exp (2 * B) * (∫ x : ℝ, ‖u x‖ ^ 2) *
                (8 * Λ * Real.exp (-(1 / 4) * h)) :=
              mul_le_mul_of_nonneg_left hlevy_min (by positivity)
          _ = C_exp * Real.exp (-(1 / 4) * h) := by dsimp [C_exp]; ring
      have hreal : archLevyDensity h * (∫ x : ℝ, ‖g x - g (x + h)‖ ^ 2) ≤
          2 * Real.exp (2 * B) * (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) +
            C_exp * Real.exp (-(1 / 4) * h) := by
        linarith
      have hnn1 : 0 ≤ 2 * Real.exp (2 * B) *
          (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) :=
        mul_nonneg (by positivity) (mul_nonneg (archLevyDensity_pos hh0).le
          (integral_nonneg fun x : ℝ => sq_nonneg ‖u x - u (x + h)‖))
      have hnn2 : 0 ≤ C_exp * Real.exp (-(1 / 4) * h) := by positivity
      calc ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖g x - g (x + h)‖ ^ 2)
          ≤ ENNReal.ofReal (2 * Real.exp (2 * B) *
              (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) +
                C_exp * Real.exp (-(1 / 4) * h)) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (2 * Real.exp (2 * B)) *
              ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) +
            ENNReal.ofReal (C_exp * Real.exp (-(1 / 4) * h)) := by
            rw [ENNReal.ofReal_add hnn1 hnn2, ENNReal.ofReal_mul (by positivity)]
    have hmeas2 : Measurable (fun h : ℝ => ENNReal.ofReal (C_exp * Real.exp (-(1 / 4) * h))) := by
      fun_prop
    have htail_lint : ∫⁻ h : ℝ in Ioi 0, ENNReal.ofReal (C_exp * Real.exp (-(1 / 4) * h)) =
        ENNReal.ofReal (C_exp * expQuarterTail) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_expQuarter.const_mul C_exp)
        (Eventually.of_forall fun h => mul_nonneg hC_exp_nn (Real.exp_pos _).le)]
      rw [integral_const_mul]
      rfl
    calc ∫⁻ h : ℝ in Ioi 0, ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖g x - g (x + h)‖ ^ 2)
        ≤ ∫⁻ h : ℝ in Ioi 0,
            (ENNReal.ofReal (2 * Real.exp (2 * B)) *
                ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2) +
              ENNReal.ofReal (C_exp * Real.exp (-(1 / 4) * h))) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = ENNReal.ofReal (2 * Real.exp (2 * B)) *
            (∫⁻ h : ℝ in Ioi 0,
              ENNReal.ofReal (archLevyDensity h * ∫ x : ℝ, ‖u x - u (x + h)‖ ^ 2)) +
          ENNReal.ofReal (C_exp * expQuarterTail) := by
          rw [lintegral_add_right _ hmeas2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            htail_lint]
      _ = ENNReal.ofReal (2 * Real.exp (2 * B) * (∫ ξ : ℝ, smoothGammaExcess u ξ) +
            16 * Λ * expQuarterTail * Real.exp (2 * B) * ∫ x : ℝ, ‖u x‖ ^ 2) := by
          rw [← ofReal_integral_smoothGammaExcess_eq_lintegral u,
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg hC_exp_nn hQ_nn)]
          congr 1
          dsimp [C_exp]
          ring
  rw [norm_sq_toCCMFormVector_eq_mass_add_excess g,
    norm_sq_toCCMFormVector_eq_mass_add_excess u]
  have hexp_pos : 0 ≤ Real.exp (2 * B) := (Real.exp_pos _).le
  have hQ_nn := expQuarterTail_nonneg
  nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 16 * Λ * expQuarterTail) hexp_pos) hE_nn,
    mul_nonneg hexp_pos hM_nn]

/-! ## 3. Rotated holomorphic disk sampling and unconditional Birman–Schwinger form bounds -/

/-- Entire rotated Fourier-Laplace transform `s ↦ testTransform ψ (-i s)`. -/
def rotatedTestTransform (ψ : ℝ → ℂ) (s : ℂ) : ℂ :=
  testTransform ψ (-Complex.I * s)

theorem differentiable_rotatedTestTransform {ψ : ℝ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) :
    Differentiable ℂ (rotatedTestTransform ψ) :=
  (differentiable_testTransform hc hs).comp (differentiable_id.const_mul (-Complex.I))

theorem rotatedTestTransform_eq_fourier_expTiltSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (η ξ : ℝ) :
    rotatedTestTransform (u : ℝ → ℂ) ((η : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I) =
      𝓕 (expTiltSource u η : ℝ → ℂ) ξ := by
  rw [fourier_eq_paperFT_neg_two_pi_mul]
  unfold rotatedTestTransform testTransform paperFT
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [expTiltSource_apply, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  calc Complex.I * (-Complex.I * (((η : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I) * (x : ℂ)))
      = -(Complex.I ^ 2) * (((η : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I) * (x : ℂ)) := by
          ring
    _ = ((η * x : ℝ) : ℂ) + Complex.I * (((-(2 * (Real.pi * ξ)) : ℝ) : ℂ) * (x : ℂ)) := by
          rw [Complex.I_sq]
          push_cast
          ring

private def verticalLogScale : ℝ := 1 + Real.log (2 + 2 * Real.pi)

private theorem verticalLogScale_pos : 0 < verticalLogScale := by
  have h := Real.log_nonneg (show 1 ≤ 2 + 2 * Real.pi by linarith [Real.pi_pos])
  unfold verticalLogScale
  linarith

private theorem vertical_scaled_weight_le (ξ : ℝ) :
    1 + Real.log (2 + |-(2 * Real.pi) * ξ|) ≤ verticalLogScale * suzukiLogWeight ξ := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ha : 0 ≤ Real.log (2 + 2 * Real.pi) := Real.log_nonneg (by linarith)
  rw [abs_mul, abs_neg, abs_of_pos hp]
  by_cases hx : |ξ| ≤ 1
  · have hl : Real.log (2 + (2 * Real.pi) * |ξ|) ≤ Real.log (2 + 2 * Real.pi) :=
      Real.log_le_log (by positivity) (by nlinarith)
    calc 1 + Real.log (2 + (2 * Real.pi) * |ξ|)
        ≤ verticalLogScale := by unfold verticalLogScale; linarith only [hl]
      _ ≤ verticalLogScale * suzukiLogWeight ξ :=
          le_mul_of_one_le_right verticalLogScale_pos.le (one_le_suzukiLogWeight ξ)
  · have hx' : 1 < |ξ| := lt_of_not_ge hx
    have hl : Real.log (2 + (2 * Real.pi) * |ξ|) ≤
        Real.log (2 + 2 * Real.pi) + Real.log |ξ| := by
      rw [← Real.log_mul (by positivity : 2 + 2 * Real.pi ≠ 0) (by positivity : |ξ| ≠ 0)]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hxlog : 0 ≤ Real.log |ξ| := Real.log_nonneg hx'.le
    rw [suzukiLogWeight, max_eq_left hxlog]
    unfold verticalLogScale
    nlinarith [mul_nonneg ha hxlog]

private theorem integrable_suzukiLogWeight_mul_fourier {a : SuzukiPositiveAperture}
    (v : CCMComplexSmoothInteriorSource a) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖𝓕 (v : ℝ → ℂ) ξ‖ ^ 2) := by
  have hcont : Continuous (fun ξ : ℝ => suzukiLogWeight ξ * ‖𝓕 (v : ℝ → ℂ) ξ‖ ^ 2) := by
    unfold suzukiLogWeight
    have hlog_cont : Continuous (fun ξ : ℝ => max (Real.log |ξ|) 0) := by
      have : (fun ξ : ℝ => max (Real.log |ξ|) 0) =
          fun ξ : ℝ => Real.log (max |ξ| 1) := by
        funext ξ
        by_cases h1 : 1 ≤ |ξ|
        · rw [max_eq_left h1, max_eq_left (Real.log_nonneg h1)]
        · have hle : |ξ| ≤ 1 := le_of_not_ge h1
          rw [max_eq_right hle, Real.log_one, max_eq_right (Real.log_nonpos (abs_nonneg ξ) hle)]
      rw [this]
      exact Continuous.log (continuous_abs.max continuous_const) fun ξ =>
        (lt_of_lt_of_le zero_lt_one (le_max_right |ξ| 1)).ne'
    exact (continuous_const.add hlog_cont).mul
      ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable v.integrable).norm.pow 2)
  refine ((integrable_ccmFormWeight_mul_norm_sq_fourier v).const_mul
    ccmArchimedeanLogComparisonConstant).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [] with ξ
  have hnn : 0 ≤ suzukiLogWeight ξ * ‖𝓕 (v : ℝ → ℂ) ξ‖ ^ 2 :=
    mul_nonneg (zero_le_one.trans (one_le_suzukiLogWeight ξ)) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact (mul_le_mul_of_nonneg_right
    (suzukiLogWeight_le_ccmArchimedeanComparison ξ) (sq_nonneg _)).trans_eq (by ring)

private def rotatedVerticalDensity (ψ : ℝ → ℂ) (η t : ℝ) : ℝ :=
  (1 + Real.log (2 + |t|)) * ‖rotatedTestTransform ψ ((η : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

private theorem rotatedVerticalDensity_nonneg (ψ : ℝ → ℂ) (η t : ℝ) :
    0 ≤ rotatedVerticalDensity ψ η t := by
  unfold rotatedVerticalDensity
  have hl : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  positivity

private theorem rotatedVerticalDensity_continuous {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Continuous (fun p : ℝ × ℝ => rotatedVerticalDensity (u : ℝ → ℂ) p.1 p.2) := by
  have hG : Continuous (rotatedTestTransform (u : ℝ → ℂ)) :=
    (differentiable_rotatedTestTransform u.continuous u.hasCompactSupport).continuous
  have hcoord : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hlog : Continuous (fun p : ℝ × ℝ => Real.log (2 + |p.2|)) :=
    Continuous.log (by fun_prop) fun _ => by positivity
  exact (continuous_const.add hlog).mul ((hG.comp hcoord).norm.pow 2)

private theorem rotatedVerticalDensity_integrable_and_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (η : ℝ) :
    Integrable (rotatedVerticalDensity (u : ℝ → ℂ) η) ∧
      (∫ t : ℝ, rotatedVerticalDensity (u : ℝ → ℂ) η t) ≤
        (2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant) *
          ‖(expTiltSource u η).toCCMFormVector‖ ^ 2 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hC_log_pos : 0 ≤ ccmArchimedeanLogComparisonConstant :=
    zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant
  have hcont_t : Continuous (rotatedVerticalDensity (u : ℝ → ℂ) η) :=
    (rotatedVerticalDensity_continuous u).comp (continuous_const.prodMk continuous_id)
  have hpt_le : ∀ ξ : ℝ,
      rotatedVerticalDensity (u : ℝ → ℂ) η (-(2 * Real.pi) * ξ) ≤
        verticalLogScale * (suzukiLogWeight ξ * ‖𝓕 (expTiltSource u η : ℝ → ℂ) ξ‖ ^ 2) := by
    intro ξ
    unfold rotatedVerticalDensity
    rw [rotatedTestTransform_eq_fourier_expTiltSource]
    exact (mul_le_mul_of_nonneg_right (vertical_scaled_weight_le ξ) (sq_nonneg _)).trans_eq (by ring)
  have his : Integrable (fun ξ : ℝ =>
      rotatedVerticalDensity (u : ℝ → ℂ) η (-(2 * Real.pi) * ξ)) := by
    refine ((integrable_suzukiLogWeight_mul_fourier (expTiltSource u η)).const_mul
      verticalLogScale).mono'
      (hcont_t.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (rotatedVerticalDensity_nonneg _ _ _)]
    exact hpt_le ξ
  have hi : Integrable (rotatedVerticalDensity (u : ℝ → ℂ) η) :=
    (integrable_comp_mul_left_iff _ (neg_ne_zero.mpr hp.ne')).mp his
  refine ⟨hi, ?_⟩
  have hb := integral_mono his
    ((integrable_suzukiLogWeight_mul_fourier (expTiltSource u η)).const_mul verticalLogScale) hpt_le
  rw [integral_const_mul] at hb
  have hsuz_le : (∫ ξ : ℝ, suzukiLogWeight ξ * ‖𝓕 (expTiltSource u η : ℝ → ℂ) ξ‖ ^ 2) ≤
      ccmArchimedeanLogComparisonConstant * ‖(expTiltSource u η).toCCMFormVector‖ ^ 2 := by
    rw [norm_sq_toCCMFormVector_eq_integral, ← integral_const_mul]
    refine integral_mono (integrable_suzukiLogWeight_mul_fourier (expTiltSource u η))
      ((integrable_ccmFormWeight_mul_norm_sq_fourier (expTiltSource u η)).const_mul _) fun ξ => ?_
    exact (mul_le_mul_of_nonneg_right
      (suzukiLogWeight_le_ccmArchimedeanComparison ξ) (sq_nonneg _)).trans_eq (by ring)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hsuz_le verticalLogScale_pos.le)
  have he := Measure.integral_comp_mul_left (rotatedVerticalDensity (u : ℝ → ℂ) η) (-(2 * Real.pi))
  simp only [abs_inv, abs_neg, abs_of_pos hp, smul_eq_mul] at he
  have hs : (∫ t : ℝ, rotatedVerticalDensity (u : ℝ → ℂ) η t) =
      (2 * Real.pi) * ∫ ξ : ℝ, rotatedVerticalDensity (u : ℝ → ℂ) η (-(2 * Real.pi) * ξ) := by
    rw [he]
    field_simp
  rw [hs]
  exact (mul_le_mul_of_nonneg_left hb' hp.le).trans_eq (by ring)

private def rotatedStrip (Λ : ℝ) : Set ℂ := {z : ℂ | z.re ∈ Icc (-Λ) Λ}

private def rotatedStripDensity (ψ : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℝ :=
  (rotatedStrip Λ).indicator
    (fun z : ℂ => (1 + Real.log (2 + |z.im|)) * ‖rotatedTestTransform ψ z‖ ^ 2) s

private def rotatedStripProductDensity (ψ : ℝ → ℂ) (Λ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Icc (-Λ) Λ).indicator (fun η => rotatedVerticalDensity ψ η p.2) p.1

private theorem rotatedStripProductDensity_nonneg (ψ : ℝ → ℂ) (Λ : ℝ) (p : ℝ × ℝ) :
    0 ≤ rotatedStripProductDensity ψ Λ p := by
  classical
  by_cases hp : p.1 ∈ Icc (-Λ) Λ
  · simpa only [rotatedStripProductDensity, indicator_of_mem hp] using
      rotatedVerticalDensity_nonneg ψ p.1 p.2
  · simp only [rotatedStripProductDensity, indicator_of_notMem hp, le_refl]

private theorem rotatedStripProductDensity_measurable {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (Λ : ℝ) :
    Measurable (rotatedStripProductDensity (u : ℝ → ℂ) Λ) := by
  classical
  let S : Set (ℝ × ℝ) := Icc (-Λ) Λ ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hm := (rotatedVerticalDensity_continuous u).continuousOn.measurable_piecewise
    (show ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Sᶜ from continuous_const.continuousOn) hS
  convert hm using 1
  funext p
  by_cases hp : p.1 ∈ Icc (-Λ) Λ
  · simp [rotatedStripProductDensity, S, hp]
  · simp [rotatedStripProductDensity, S, hp]

private theorem rotatedStripProductDensity_coordinates (ψ : ℝ → ℂ) (Λ : ℝ) (s : ℂ) :
    rotatedStripProductDensity ψ Λ (s.re, s.im) = rotatedStripDensity ψ Λ s := by
  classical
  by_cases hs : s ∈ rotatedStrip Λ
  · have hr : s.re ∈ Icc (-Λ) Λ := hs
    simp only [rotatedStripProductDensity, indicator_of_mem hr, rotatedStripDensity,
      indicator_of_mem hs, rotatedVerticalDensity, Complex.re_add_im]
  · have hr : s.re ∉ Icc (-Λ) Λ := hs
    simp only [rotatedStripProductDensity, indicator_of_notMem hr, rotatedStripDensity,
      indicator_of_notMem hs]

private theorem rotatedStrip_integrable_and_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {Λ B : ℝ} (hΛ : 0 ≤ Λ) (hB : Λ * a.1 ≤ B) :
    Integrable (rotatedStripDensity (u : ℝ → ℂ) Λ) ∧
      (∫ s : ℂ, rotatedStripDensity (u : ℝ → ℂ) Λ s) ≤
        (2 * Λ) * ((2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant) *
          (Real.exp (2 * B) * (2 + 16 * Λ * expQuarterTail) * ‖u.toCCMFormVector‖ ^ 2)) := by
  classical
  let M_line : ℝ := (2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant) *
    (Real.exp (2 * B) * (2 + 16 * Λ * expQuarterTail) * ‖u.toCCMFormVector‖ ^ 2)
  let b : ℝ → ℝ := (Icc (-Λ) Λ).indicator (fun _ => M_line)
  have hb : Integrable b := (integrable_indicator_iff measurableSet_Icc).mpr
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
  have hline_int : ∀ η : ℝ, Integrable (fun t : ℝ =>
      rotatedStripProductDensity (u : ℝ → ℂ) Λ (η, t)) := fun η => by
    by_cases hη : η ∈ Icc (-Λ) Λ
    · simpa only [rotatedStripProductDensity, indicator_of_mem hη] using
        (rotatedVerticalDensity_integrable_and_le u η).1
    · simp only [rotatedStripProductDensity, indicator_of_notMem hη]
      exact integrable_zero _ _ _
  have hline_le : ∀ η : ℝ,
      (∫ t : ℝ, rotatedStripProductDensity (u : ℝ → ℂ) Λ (η, t)) ≤ b η := fun η => by
    by_cases hη : η ∈ Icc (-Λ) Λ
    · simp only [rotatedStripProductDensity, b, indicator_of_mem hη]
      have hη_abs : |η| ≤ Λ := abs_le.mpr hη
      have h1 := (rotatedVerticalDensity_integrable_and_le u η).2
      have h2 := norm_sq_expTiltSource_toCCMFormVector_le u hη_abs hΛ hB
      have hC_pos : 0 ≤ 2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant :=
        mul_nonneg (mul_nonneg (by positivity) verticalLogScale_pos.le)
          (zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hC_pos)
    · simp only [rotatedStripProductDensity, b, indicator_of_notMem hη, integral_zero, le_refl]
  have hm : AEStronglyMeasurable (rotatedStripProductDensity (u : ℝ → ℂ) Λ)
      ((volume : Measure ℝ).prod volume) :=
    (rotatedStripProductDensity_measurable u Λ).aestronglyMeasurable
  have hnorm : (fun η : ℝ => ∫ t : ℝ, ‖rotatedStripProductDensity (u : ℝ → ℂ) Λ (η, t)‖) =
      fun η : ℝ => ∫ t : ℝ, rotatedStripProductDensity (u : ℝ → ℂ) Λ (η, t) := by
    funext η
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact Real.norm_of_nonneg (rotatedStripProductDensity_nonneg _ _ _)
  have hout : Integrable (fun η : ℝ =>
      ∫ t : ℝ, ‖rotatedStripProductDensity (u : ℝ → ℂ) Λ (η, t)‖) := by
    refine hb.mono' hm.norm.integral_prod_right' (Eventually.of_forall fun η => ?_)
    rw [congrFun hnorm η, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun t => rotatedStripProductDensity_nonneg _ _ _)]
    exact hline_le η
  have hi_prod : Integrable (rotatedStripProductDensity (u : ℝ → ℂ) Λ) :=
    (integrable_prod_iff hm).mpr ⟨Eventually.of_forall hline_int, hout⟩
  have hi_complex : Integrable (rotatedStripDensity (u : ℝ → ℂ) Λ) := by
    have h := Complex.volume_preserving_equiv_real_prod.integrable_comp_of_integrable hi_prod
    simpa only [Function.comp_def, Complex.measurableEquivRealProd_apply,
      rotatedStripProductDensity_coordinates] using h
  refine ⟨hi_complex, ?_⟩
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (rotatedStripProductDensity (u : ℝ → ℂ) Λ)
  simp only [Complex.measurableEquivRealProd_apply, rotatedStripProductDensity_coordinates] at he
  rw [he, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, integral_prod _ hi_prod]
  have hbound := integral_mono hi_prod.integral_prod_left hb hline_le
  have hb_int : (∫ η : ℝ, b η) = (2 * Λ) * M_line := by
    dsimp [b]
    rw [integral_indicator_const _ measurableSet_Icc]
    simp only [Measure.real, Real.volume_Icc, show Λ - -Λ = 2 * Λ by ring, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith)]
  rwa [hb_int] at hbound

private theorem zetaZeroWidth_le_one_half : zetaZeroWidth ≤ 1 / 2 :=
  (zetaZeroWidth_le_iff_re_le (by norm_num)).mpr fun ρ hρ => by linarith [hρ.2.2]

open scoped Classical in
private theorem rotatedDiskOverlap_le {w : XiZeroCopy → ℂ} {r C_pkt : ℝ}
    (hr_le : r ≤ 1)
    (hw_re : ∀ q : XiZeroCopy, |(w q).re| ≤ zetaZeroWidth)
    (hw_im : ∀ q : XiZeroCopy, (w q).im = -(q.1 : ℂ).im)
    (hpkt : ∀ T : ℝ, ((xiUnitHeightPacket T).card : ℝ) ≤ C_pkt * (1 + Real.log (2 + |T|)))
    (F : Finset XiZeroCopy) (s : ℂ) :
    (∑ q ∈ F, (if s ∈ Metric.ball (w q) r then (1 : ℝ) else 0)) ≤
      (rotatedStrip (zetaZeroWidth + r)).indicator
        (fun z : ℂ => C_pkt * (1 + Real.log (2 + |z.im|))) s := by
  have hmem_strip : ∀ q : XiZeroCopy, s ∈ Metric.ball (w q) r →
      s ∈ rotatedStrip (zetaZeroWidth + r) := by
    intro q hs
    have hd : ‖s - w q‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hs
    have hre := abs_le.mp ((Complex.abs_re_le_norm (s - w q)).trans hd.le)
    simp only [Complex.sub_re] at hre
    have hwq := abs_le.mp (hw_re q)
    exact ⟨by linarith, by linarith⟩
  by_cases hs : s ∈ rotatedStrip (zetaZeroWidth + r)
  · rw [indicator_of_mem hs]
    have hcard_eq : (∑ q ∈ F, (if s ∈ Metric.ball (w q) r then (1 : ℝ) else 0)) =
        ((F.filter fun q => s ∈ Metric.ball (w q) r).card : ℝ) := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard_eq]
    have hsub : (F.filter fun q => s ∈ Metric.ball (w q) r).card ≤
        (xiUnitHeightPacket (-s.im)).card := by
      refine Finset.card_le_card fun q hq => ?_
      have hd : ‖s - w q‖ < r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using (Finset.mem_filter.mp hq).2
      rw [mem_xiUnitHeightPacket]
      have him := (Complex.abs_im_le_norm (s - w q)).trans (hd.le.trans hr_le)
      simp only [Complex.sub_im, hw_im q, sub_neg_eq_add] at him
      rwa [show (q.1 : ℂ).im - -s.im = s.im + (q.1 : ℂ).im by ring]
    have h1 : ((F.filter fun q => s ∈ Metric.ball (w q) r).card : ℝ) ≤
        ((xiUnitHeightPacket (-s.im)).card : ℝ) := Nat.cast_le.mpr hsub
    exact h1.trans ((hpkt (-s.im)).trans_eq (by rw [abs_neg]))
  · rw [indicator_of_notMem hs, Finset.sum_eq_zero]
    intro q _
    exact if_neg fun h => hs (hmem_strip q h)

private theorem sum_norm_sq_rotatedTestTransform_le {C_pkt : ℝ} (hC_pkt : 0 < C_pkt)
    (hpkt : ∀ T : ℝ, ((xiUnitHeightPacket T).card : ℝ) ≤ C_pkt * (1 + Real.log (2 + |T|)))
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    {w : XiZeroCopy → ℂ}
    (hw_re : ∀ q : XiZeroCopy, |(w q).re| ≤ zetaZeroWidth)
    (hw_im : ∀ q : XiZeroCopy, (w q).im = -(q.1 : ℂ).im)
    (F : Finset XiZeroCopy) :
    (∑ q ∈ F, ‖rotatedTestTransform (u : ℝ → ℂ) (w q)‖ ^ 2) ≤
      (6 * verticalLogScale * ccmArchimedeanLogComparisonConstant *
        Real.exp 2 * (2 + 24 * expQuarterTail) * C_pkt) *
        max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) * ‖u.toCCMFormVector‖ ^ 2 := by
  classical
  let r : ℝ := 1 / max a.1 1
  have hmax_ge1 : 1 ≤ max a.1 1 := le_max_right a.1 1
  have hmax_pos : 0 < max a.1 1 := lt_of_lt_of_le zero_lt_one hmax_ge1
  have hr_pos : 0 < r := div_pos one_pos hmax_pos
  have hr_le : r ≤ 1 := div_le_one_of_le₀ hmax_ge1 hmax_pos.le
  let Λ : ℝ := zetaZeroWidth + r
  have hΛ_nn : 0 ≤ Λ := add_nonneg zetaZeroWidth_nonneg hr_pos.le
  have hΛ_le : Λ ≤ 3 / 2 := by linarith [zetaZeroWidth_le_one_half]
  let B : ℝ := zetaZeroWidth * a.1 + 1
  have hB_ge : Λ * a.1 ≤ B := by
    have hra : r * a.1 ≤ 1 := by
      dsimp [r]
      rw [one_div_mul_eq_div]
      exact div_le_one_of_le₀ (le_max_left a.1 1) hmax_pos.le
    dsimp [Λ, B]
    nlinarith
  have hG_diff : Differentiable ℂ (rotatedTestTransform (u : ℝ → ℂ)) :=
    differentiable_rotatedTestTransform u.continuous u.hasCompactSupport
  let ballInd : XiZeroCopy → ℂ → ℝ := fun q =>
    (Metric.ball (w q) r).indicator (fun s : ℂ => ‖rotatedTestTransform (u : ℝ → ℂ) s‖ ^ 2)
  have hball_int : ∀ q : XiZeroCopy, Integrable (ballInd q) := fun q => by
    refine (integrable_indicator_iff measurableSet_ball).mpr ?_
    exact ((hG_diff.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (w q) r)).mono_set ball_subset_closedBall
  have hpt_overlap : ∀ s : ℂ, (∑ q ∈ F, ballInd q s) ≤
      C_pkt * rotatedStripDensity (u : ℝ → ℂ) Λ s := fun s => by
    have hsum_eq : (∑ q ∈ F, ballInd q s) =
        (∑ q ∈ F, (if s ∈ Metric.ball (w q) r then (1 : ℝ) else 0)) *
          ‖rotatedTestTransform (u : ℝ → ℂ) s‖ ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hs : s ∈ Metric.ball (w q) r
      · simp only [ballInd, indicator_of_mem hs, if_pos hs, one_mul]
      · simp only [ballInd, indicator_of_notMem hs, if_neg hs, zero_mul]
    rw [hsum_eq]
    have hov := mul_le_mul_of_nonneg_right
      (rotatedDiskOverlap_le hr_le hw_re hw_im hpkt F s)
      (sq_nonneg ‖rotatedTestTransform (u : ℝ → ℂ) s‖)
    refine hov.trans_eq ?_
    change (rotatedStrip Λ).indicator
        (fun z : ℂ => C_pkt * (1 + Real.log (2 + |z.im|))) s *
        ‖rotatedTestTransform (u : ℝ → ℂ) s‖ ^ 2 =
      C_pkt * rotatedStripDensity (u : ℝ → ℂ) Λ s
    by_cases hs : s ∈ rotatedStrip Λ
    · simp only [rotatedStripDensity, indicator_of_mem hs]
      ring
    · simp only [rotatedStripDensity, indicator_of_notMem hs, zero_mul, mul_zero]
  have hstrip := rotatedStrip_integrable_and_le u hΛ_nn hB_ge
  have harea_le : (Real.pi * r ^ 2) * (∑ q ∈ F, ‖rotatedTestTransform (u : ℝ → ℂ) (w q)‖ ^ 2) ≤
      C_pkt * ∫ s : ℂ, rotatedStripDensity (u : ℝ → ℂ) Λ s := by
    calc (Real.pi * r ^ 2) * (∑ q ∈ F, ‖rotatedTestTransform (u : ℝ → ℂ) (w q)‖ ^ 2)
        = ∑ q ∈ F, Real.pi * r ^ 2 * ‖rotatedTestTransform (u : ℝ → ℂ) (w q)‖ ^ 2 :=
          Finset.mul_sum ..
      _ ≤ ∑ q ∈ F, ∫ s in Metric.ball (w q) r, ‖rotatedTestTransform (u : ℝ → ℂ) s‖ ^ 2 :=
          Finset.sum_le_sum fun q _ =>
            normSq_value_mul_area_le_integral_ball _ hG_diff (w q) hr_pos
      _ = ∑ q ∈ F, ∫ s : ℂ, ballInd q s :=
          Finset.sum_congr rfl fun q _ => (integral_indicator measurableSet_ball).symm
      _ = ∫ s : ℂ, ∑ q ∈ F, ballInd q s :=
          (integral_finsetSum F fun q _ => hball_int q).symm
      _ ≤ ∫ s : ℂ, C_pkt * rotatedStripDensity (u : ℝ → ℂ) Λ s :=
          integral_mono (integrable_finsetSum F fun q _ => hball_int q)
            (hstrip.1.const_mul C_pkt) hpt_overlap
      _ = C_pkt * ∫ s : ℂ, rotatedStripDensity (u : ℝ → ℂ) Λ s :=
          integral_const_mul C_pkt _
  have hstrip_cap : C_pkt * (∫ s : ℂ, rotatedStripDensity (u : ℝ → ℂ) Λ s) ≤
      (Real.pi * r ^ 2) * ((6 * verticalLogScale * ccmArchimedeanLogComparisonConstant *
        Real.exp 2 * (2 + 24 * expQuarterTail) * C_pkt) *
        max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) * ‖u.toCCMFormVector‖ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hstrip.2 hC_pkt.le
    have hexpB_eq : Real.exp (2 * B) = Real.exp 2 * Real.exp (2 * zetaZeroWidth * a.1) := by
      dsimp [B]
      rw [show 2 * (zetaZeroWidth * a.1 + 1) = 2 + 2 * zetaZeroWidth * a.1 by ring, Real.exp_add]
    have hr_cancel : r ^ 2 * max a.1 1 ^ 2 = 1 := by
      dsimp [r]
      field_simp [hmax_pos.ne']
    have h2Λ : 2 * Λ ≤ 3 := by linarith
    have h16Λ : 2 + 16 * Λ * expQuarterTail ≤ 2 + 24 * expQuarterTail := by
      have hQ := expQuarterTail_nonneg
      nlinarith
    have hC_pos : 0 ≤ 2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant :=
      mul_nonneg (mul_nonneg (by positivity) verticalLogScale_pos.le)
        (zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant)
    have hQ := expQuarterTail_nonneg
    have hfactor : (2 * Λ) * (2 + 16 * Λ * expQuarterTail) ≤ 3 * (2 + 24 * expQuarterTail) :=
      mul_le_mul h2Λ h16Λ (by positivity) (by norm_num)
    have hnonneg_rest : 0 ≤ C_pkt * (2 * Real.pi * verticalLogScale *
        ccmArchimedeanLogComparisonConstant) * Real.exp (2 * B) * ‖u.toCCMFormVector‖ ^ 2 := by
      positivity
    calc C_pkt * (∫ s : ℂ, rotatedStripDensity (u : ℝ → ℂ) Λ s)
        ≤ C_pkt * ((2 * Λ) * ((2 * Real.pi * verticalLogScale *
            ccmArchimedeanLogComparisonConstant) *
            (Real.exp (2 * B) * (2 + 16 * Λ * expQuarterTail) * ‖u.toCCMFormVector‖ ^ 2))) := h1
      _ = ((2 * Λ) * (2 + 16 * Λ * expQuarterTail)) *
            (C_pkt * (2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant) *
              Real.exp (2 * B) * ‖u.toCCMFormVector‖ ^ 2) := by ring
      _ ≤ (3 * (2 + 24 * expQuarterTail)) *
            (C_pkt * (2 * Real.pi * verticalLogScale * ccmArchimedeanLogComparisonConstant) *
              Real.exp (2 * B) * ‖u.toCCMFormVector‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hfactor hnonneg_rest
      _ = (Real.pi * (r ^ 2 * max a.1 1 ^ 2)) *
            ((6 * verticalLogScale * ccmArchimedeanLogComparisonConstant *
              Real.exp 2 * (2 + 24 * expQuarterTail) * C_pkt) *
              Real.exp (2 * zetaZeroWidth * a.1) * ‖u.toCCMFormVector‖ ^ 2) := by
          rw [hr_cancel, mul_one, hexpB_eq]
          ring
      _ = (Real.pi * r ^ 2) * ((6 * verticalLogScale * ccmArchimedeanLogComparisonConstant *
            Real.exp 2 * (2 + 24 * expQuarterTail) * C_pkt) *
            max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) * ‖u.toCCMFormVector‖ ^ 2) := by
          ring
  exact le_of_mul_le_mul_left (harea_le.trans hstrip_cap)
    (mul_pos Real.pi_pos (pow_pos hr_pos 2))

private theorem norm_le_of_isSelfAdjoint_re_inner_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ v : H, |(inner ℂ (T v) v).re| ≤ M * ‖v‖ ^ 2) :
    ‖T‖ ≤ M := by
  have hsymm : (T : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsymm]
  refine ciSup_le fun v => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  by_cases hv : v = 0
  · simp [hv, hM]
  · have hpos : 0 < ‖v‖ ^ 2 := by positivity
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h v

/-- **Unconditional form-domain zero-pair, quadratic-form, and Birman–Schwinger norm theorem.**
Without any off-line zero-clustering hypothesis, there is one universal constant `K > 0` such that
at every aperture `a > 0`:
1. both `pairedPlusEnergy u` and `pairedMinusEnergy u` are bounded by
   `K * max a.1 1 ^ 2 * e^{2 * zetaZeroWidth * a.1} * ‖u.toCCMFormVector‖ ^ 2` for every smooth
   interior source `u`;
2. `|ccmRestrictedWeilSourceQuadratic a v| ≤ K * max a.1 1 ^ 2 * e^{2 * zetaZeroWidth * a.1} * ‖v‖ ^ 2`
   for every `v : CCMArchimedeanFormDomain a`;
3. `‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ ≤ 1 + K * max a.1 1 ^ 2 * e^{2 * zetaZeroWidth * a.1}`. -/
theorem exists_unconditional_pairedEnergy_and_birmanSchwinger_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ a : SuzukiPositiveAperture,
      (∀ u : CCMComplexSmoothInteriorSource a,
        pairedPlusEnergy u ≤
          K * max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) * ‖u.toCCMFormVector‖ ^ 2 ∧
        pairedMinusEnergy u ≤
          K * max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) * ‖u.toCCMFormVector‖ ^ 2) ∧
      (∀ v : CCMArchimedeanFormDomain a,
        |ccmRestrictedWeilSourceQuadratic a v| ≤
          K * max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) * ‖v‖ ^ 2) ∧
      ‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ ≤
        1 + K * max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) := by
  obtain ⟨C_pkt, hC_pkt, hpkt⟩ := exists_xiUnitHeightPacket_global_log_bound
  have hQ_nn := expQuarterTail_nonneg
  have hC_log_pos : 0 < ccmArchimedeanLogComparisonConstant :=
    lt_of_lt_of_le zero_lt_one one_le_ccmArchimedeanLogComparisonConstant
  obtain ⟨K, hK_pos, hK_def⟩ : ∃ K : ℝ, 0 < K ∧
      K = 6 * verticalLogScale * ccmArchimedeanLogComparisonConstant *
        Real.exp 2 * (2 + 24 * expQuarterTail) * C_pkt :=
    ⟨_, by have := verticalLogScale_pos; positivity, rfl⟩
  refine ⟨K, hK_pos, fun a => ?_⟩
  let M_a : ℝ := K * max a.1 1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1)
  have hM_a_pos : 0 < M_a := by
    dsimp [M_a]
    have hmax : 0 < max a.1 1 := lt_of_lt_of_le zero_lt_one (le_max_right a.1 1)
    positivity
  have hsmooth : ∀ u : CCMComplexSmoothInteriorSource a,
      pairedPlusEnergy u ≤ M_a * ‖u.toCCMFormVector‖ ^ 2 ∧
        pairedMinusEnergy u ≤ M_a * ‖u.toCCMFormVector‖ ^ 2 := by
    intro u
    let w₁ : XiZeroCopy → ℂ := fun q => Complex.I * (-xiSpectralPoint q)
    let w₂ : XiZeroCopy → ℂ := fun q => Complex.I * (-(starRingEnd ℂ) (xiSpectralPoint q))
    have hw₁_val : ∀ q : XiZeroCopy,
        rotatedTestTransform (u : ℝ → ℂ) (w₁ q) = testTransform (u : ℝ → ℂ) (-xiSpectralPoint q) := by
      intro q
      unfold rotatedTestTransform
      congr 1
      dsimp [w₁]
      rw [show -Complex.I * (Complex.I * -xiSpectralPoint q) =
        -(Complex.I ^ 2) * (-xiSpectralPoint q) by ring, Complex.I_sq]
      ring
    have hw₂_val : ∀ q : XiZeroCopy,
        rotatedTestTransform (u : ℝ → ℂ) (w₂ q) =
          testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q)) := by
      intro q
      unfold rotatedTestTransform
      congr 1
      dsimp [w₂]
      rw [show -Complex.I * (Complex.I * -(starRingEnd ℂ) (xiSpectralPoint q)) =
        -(Complex.I ^ 2) * (-(starRingEnd ℂ) (xiSpectralPoint q)) by ring, Complex.I_sq]
      ring
    have hw₁_re : ∀ q : XiZeroCopy, |(w₁ q).re| ≤ zetaZeroWidth := fun q => by
      have : (w₁ q).re = (xiSpectralPoint q).im := by simp [w₁]
      rw [this]
      exact abs_im_xiSpectralPoint_le_zetaZeroWidth q
    have hw₁_im : ∀ q : XiZeroCopy, (w₁ q).im = -(q.1 : ℂ).im := fun q => by
      simp [w₁, xiSpectralPoint]
    have hw₂_re : ∀ q : XiZeroCopy, |(w₂ q).re| ≤ zetaZeroWidth := fun q => by
      have : (w₂ q).re = -(xiSpectralPoint q).im := by simp [w₂]
      rw [this, abs_neg]
      exact abs_im_xiSpectralPoint_le_zetaZeroWidth q
    have hw₂_im : ∀ q : XiZeroCopy, (w₂ q).im = -(q.1 : ℂ).im := fun q => by
      simp [w₂, xiSpectralPoint]
    have hsum1 : ∀ F : Finset XiZeroCopy,
        (∑ q ∈ F, ‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2) ≤
          M_a * ‖u.toCCMFormVector‖ ^ 2 := fun F => by
      simp_rw [← hw₁_val]
      have h := sum_norm_sq_rotatedTestTransform_le hC_pkt hpkt u hw₁_re hw₁_im F
      rwa [← hK_def] at h
    have hsum2 : ∀ F : Finset XiZeroCopy,
        (∑ q ∈ F, ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) ≤
          M_a * ‖u.toCCMFormVector‖ ^ 2 := fun F => by
      simp_rw [← hw₂_val]
      have h := sum_norm_sq_rotatedTestTransform_le hC_pkt hpkt u hw₂_re hw₂_im F
      rwa [← hK_def] at h
    have hfin_plus : ∀ F : Finset XiZeroCopy,
        (∑ q ∈ F, pairedPlusTerm u q) ≤ M_a * ‖u.toCCMFormVector‖ ^ 2 := fun F => by
      have hpt : ∀ q : XiZeroCopy, pairedPlusTerm u q ≤
          (‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2 +
            ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) / 2 := by
        intro q
        unfold pairedPlusTerm
        have htri := norm_add_le (testTransform (u : ℝ → ℂ) (-xiSpectralPoint q))
          (testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q)))
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ -
          ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]
      have hle := Finset.sum_le_sum fun q (_ : q ∈ F) => hpt q
      simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div] at hle
      linarith [hsum1 F, hsum2 F]
    have hfin_minus : ∀ F : Finset XiZeroCopy,
        (∑ q ∈ F, pairedMinusTerm u q) ≤ M_a * ‖u.toCCMFormVector‖ ^ 2 := fun F => by
      have hpt : ∀ q : XiZeroCopy, pairedMinusTerm u q ≤
          (‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2 +
            ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) / 2 := by
        intro q
        unfold pairedMinusTerm
        have htri := norm_sub_le (testTransform (u : ℝ → ℂ) (-xiSpectralPoint q))
          (testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q)))
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ -
          ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]
      have hle := Finset.sum_le_sum fun q (_ : q ∈ F) => hpt q
      simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div] at hle
      linarith [hsum1 F, hsum2 F]
    exact ⟨Real.tsum_le_of_sum_le (pairedPlusTerm_nonneg u) hfin_plus,
      Real.tsum_le_of_sum_le (pairedMinusTerm_nonneg u) hfin_minus⟩
  have hquad : ∀ v : CCMArchimedeanFormDomain a,
      |ccmRestrictedWeilSourceQuadratic a v| ≤ M_a * ‖v‖ ^ 2 := by
    intro v
    refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on v ?_ ?_
    · exact isClosed_le (continuous_ccmRestrictedWeilSourceQuadratic a).abs
        (continuous_const.mul (continuous_norm.pow 2))
    · intro u
      rw [sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy, abs_le]
      obtain ⟨hp, hm⟩ := hsmooth u
      have hp0 := pairedPlusEnergy_nonneg u
      have hm0 := pairedMinusEnergy_nonneg u
      exact ⟨by linarith, by linarith⟩
  have hBS : ‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ ≤ 1 + M_a := by
    refine norm_le_of_isSelfAdjoint_re_inner_le
      (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a 0) (by linarith) fun v => ?_
    have hid := congrArg Complex.re
      (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a v v)
    have hself : (inner ℂ v v).re = ‖v‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [ccmRestrictedWeilForm_self_re_eq_source, Complex.sub_re, hself] at hid
    have hq := abs_le.mp (hquad v)
    rw [abs_le, add_mul, one_mul]
    have hv_nn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg ‖v‖
    exact ⟨by linarith, by linarith⟩
  exact ⟨hsmooth, hquad, hBS⟩

/-! ## 4. Lag-uniform form norm of polar-free two-bump probes and exact rate equalities -/

/-- Admissible exponential lower-floor rates on the full Archimedean form domain:
`-(C e^{2σa}) ‖v‖_{Form}² ≤ Q_a(v)` for all `a ≥ A₀` and all `v`. -/
def formGroundEnergyRates : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C A₀ : ℝ, ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 →
    ∀ v : CCMArchimedeanFormDomain a,
      -(C * Real.exp (2 * σ * a.1)) * ‖v‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a v}

/-- Admissible exponential lower-floor rates on polar-constrained vectors of the form domain. -/
def polarFormGroundEnergyRates : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C A₀ : ℝ, ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 →
    ∀ v : CCMArchimedeanFormDomain a, IsPolarConstrained a v →
      -(C * Real.exp (2 * σ * a.1)) * ‖v‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a v}

/-- Admissible exponential growth rates of the zero-energy Birman–Schwinger operator norm
`‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ ≤ C e^{2σa}`. -/
def birmanSchwingerNormRates : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C A₀ : ℝ, ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 →
    ‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ ≤ C * Real.exp (2 * σ * a.1)}

/-- Exponential growth rate of the lower form-domain floor of `Q_a`. -/
def formGroundEnergyRate : ℝ := sInf formGroundEnergyRates

/-- Exponential growth rate of the polar-constrained lower form-domain floor of `Q_a`. -/
def polarFormGroundEnergyRate : ℝ := sInf polarFormGroundEnergyRates

/-- Exponential growth rate of `‖ccmRestrictedWeilFormBirmanSchwinger a 0‖`. -/
def birmanSchwingerNormRate : ℝ := sInf birmanSchwingerNormRates

private theorem bddBelow_formGroundEnergyRates : BddBelow formGroundEnergyRates :=
  ⟨0, fun _ h => h.1⟩

private theorem bddBelow_polarFormGroundEnergyRates : BddBelow polarFormGroundEnergyRates :=
  ⟨0, fun _ h => h.1⟩

private theorem bddBelow_birmanSchwingerNormRates : BddBelow birmanSchwingerNormRates :=
  ⟨0, fun _ h => h.1⟩

theorem formGroundEnergyRates_subset_polar :
    formGroundEnergyRates ⊆ polarFormGroundEnergyRates := by
  rintro σ ⟨hσ, C, A₀, hC⟩
  exact ⟨hσ, C, A₀, fun a ha v _ => hC a ha v⟩

theorem birmanSchwingerNormRates_subset_form :
    birmanSchwingerNormRates ⊆ formGroundEnergyRates := by
  rintro σ ⟨hσ, C, A₀, hC⟩
  refine ⟨hσ, C, A₀, fun a ha v => ?_⟩
  have hid := congrArg Complex.re
    (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a v v)
  have hself : (inner ℂ v v).re = ‖v‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [ccmRestrictedWeilForm_self_re_eq_source, Complex.sub_re, hself] at hid
  have hcauchy : (inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 v) v).re ≤
      ‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ * ‖v‖ ^ 2 := by
    have h1 : (inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 v) v).re ≤
        ‖ccmRestrictedWeilFormBirmanSchwinger a 0 v‖ * ‖v‖ :=
      (Complex.re_le_norm _).trans
        (norm_inner_le_norm (𝕜 := ℂ) (ccmRestrictedWeilFormBirmanSchwinger a 0 v) v)
    calc (inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 v) v).re
        ≤ ‖ccmRestrictedWeilFormBirmanSchwinger a 0 v‖ * ‖v‖ := h1
      _ ≤ (‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right
            ((ccmRestrictedWeilFormBirmanSchwinger a 0).le_opNorm v) (norm_nonneg v)
      _ = ‖ccmRestrictedWeilFormBirmanSchwinger a 0‖ * ‖v‖ ^ 2 := by ring
  have hop := mul_le_mul_of_nonneg_right (hC a ha) (sq_nonneg ‖v‖)
  have hv_nn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg ‖v‖
  linarith

/-- Every `σ > zetaZeroWidth` belongs to `birmanSchwingerNormRates` unconditionally. -/
theorem mem_birmanSchwingerNormRates_of_gt {σ : ℝ} (hσ : zetaZeroWidth < σ) :
    σ ∈ birmanSchwingerNormRates := by
  have hσ_nn : 0 ≤ σ := zetaZeroWidth_nonneg.trans hσ.le
  have hδ : 0 < σ - zetaZeroWidth := sub_pos.mpr hσ
  obtain ⟨K, hK_pos, hbounds⟩ := exists_unconditional_pairedEnergy_and_birmanSchwinger_bounds
  refine ⟨hσ_nn, 1 + K / (σ - zetaZeroWidth) ^ 2, 1, fun a ha1 => ?_⟩
  have hBS := (hbounds a).2.2
  rw [max_eq_left ha1] at hBS
  have ha_sq : a.1 ^ 2 ≤ (1 / (σ - zetaZeroWidth) ^ 2) *
      Real.exp (2 * (σ - zetaZeroWidth) * a.1) := by
    have h1 := Real.add_one_le_exp ((σ - zetaZeroWidth) * a.1)
    have hlin : (σ - zetaZeroWidth) * a.1 ≤ Real.exp ((σ - zetaZeroWidth) * a.1) := by linarith
    have hsq := pow_le_pow_left₀ (mul_nonneg hδ.le a.2.le) hlin 2
    rw [mul_pow, ← Real.exp_nat_mul] at hsq
    have hdiv := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 1 / (σ - zetaZeroWidth) ^ 2 by positivity)
    have hcancel : (1 / (σ - zetaZeroWidth) ^ 2) * ((σ - zetaZeroWidth) ^ 2 * a.1 ^ 2) =
        a.1 ^ 2 := by
      field_simp [hδ.ne']
    rw [hcancel] at hdiv
    refine hdiv.trans (le_of_eq ?_)
    rw [show ((2 : ℕ) : ℝ) * ((σ - zetaZeroWidth) * a.1) = 2 * (σ - zetaZeroWidth) * a.1 by
      push_cast; ring]
  have hexp_ge1 : 1 ≤ Real.exp (2 * σ * a.1) := Real.one_le_exp (by positivity)
  have hexp_split : Real.exp (2 * (σ - zetaZeroWidth) * a.1) * Real.exp (2 * zetaZeroWidth * a.1) =
      Real.exp (2 * σ * a.1) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖ccmRestrictedWeilFormBirmanSchwinger a 0‖
      ≤ 1 + K * a.1 ^ 2 * Real.exp (2 * zetaZeroWidth * a.1) := hBS
    _ ≤ Real.exp (2 * σ * a.1) +
          K * ((1 / (σ - zetaZeroWidth) ^ 2) * Real.exp (2 * (σ - zetaZeroWidth) * a.1)) *
            Real.exp (2 * zetaZeroWidth * a.1) :=
        add_le_add hexp_ge1 (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha_sq hK_pos.le) (Real.exp_pos _).le)
    _ = Real.exp (2 * σ * a.1) +
          (K / (σ - zetaZeroWidth) ^ 2) *
            (Real.exp (2 * (σ - zetaZeroWidth) * a.1) * Real.exp (2 * zetaZeroWidth * a.1)) := by
        ring
    _ = (1 + K / (σ - zetaZeroWidth) ^ 2) * Real.exp (2 * σ * a.1) := by
        rw [hexp_split]; ring

private theorem birmanSchwingerNormRates_nonempty : birmanSchwingerNormRates.Nonempty :=
  ⟨zetaZeroWidth + 1, mem_birmanSchwingerNormRates_of_gt (by linarith)⟩

private theorem formGroundEnergyRates_nonempty : formGroundEnergyRates.Nonempty :=
  birmanSchwingerNormRates_nonempty.mono birmanSchwingerNormRates_subset_form

private theorem polarFormGroundEnergyRates_nonempty : polarFormGroundEnergyRates.Nonempty :=
  formGroundEnergyRates_nonempty.mono formGroundEnergyRates_subset_polar

private def polarFreeBaseSource {w : ℝ} (hw : 0 < w) :
    CCMComplexSmoothInteriorSource ⟨w + 1, by linarith⟩ where
  toFun := scaledBumpPolarFree w 0
  smooth := contDiff_top_scaledBumpPolarFree w 0
  hasCompactSupport := hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw 0)
  tsupport_subset := by
    have hsub : tsupport (scaledBumpPolarFree w 0) ⊆ Icc (-w) w := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      have habs := scaledBumpPolarFree_support hw 0 x hx
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    exact hsub.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

private def polarFreeTwoBumpSource {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v) :
    CCMComplexSmoothInteriorSource ⟨v / 2 + w + 1, by linarith⟩ where
  toFun := twoBump (scaledBumpPolarFree w 0) v (-1)
  smooth := by
    unfold twoBump bumpTest
    exact ContDiff.sum fun i _ =>
      contDiff_const.mul ((contDiff_top_scaledBumpPolarFree w 0).comp
        (contDiff_id.sub contDiff_const))
  hasCompactSupport := hasCompactSupport_twoBump
    (hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw 0)) v (-1)
  tsupport_subset := (tsupport_twoBump_scaledBumpPolarFree_subset hw 0 hv (-1)).trans
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem norm_sq_polarFreeTwoBumpSource_le {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v) :
    ‖(polarFreeTwoBumpSource hw hv).toCCMFormVector‖ ^ 2 ≤
      4 * ‖(polarFreeBaseSource hw).toCCMFormVector‖ ^ 2 := by
  rw [norm_sq_toCCMFormVector_eq_integral, norm_sq_toCCMFormVector_eq_integral,
    ← integral_const_mul]
  refine integral_mono
    (integrable_ccmFormWeight_mul_norm_sq_fourier (polarFreeTwoBumpSource hw hv))
    ((integrable_ccmFormWeight_mul_norm_sq_fourier (polarFreeBaseSource hw)).const_mul 4)
    fun ξ => ?_
  have hb_cont : Continuous (scaledBumpPolarFree w 0) :=
    (contDiff_top_scaledBumpPolarFree w 0).continuous
  have hb_cs : HasCompactSupport (scaledBumpPolarFree w 0) :=
    hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw 0)
  have hft : 𝓕 (polarFreeTwoBumpSource hw hv : ℝ → ℂ) ξ =
      (cexp (-(Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))) +
        (-1 : ℂ) * cexp (Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))) *
        𝓕 (polarFreeBaseSource hw : ℝ → ℂ) ξ := by
    change 𝓕 (twoBump (scaledBumpPolarFree w 0) v (-1)) ξ =
      _ * 𝓕 (scaledBumpPolarFree w 0) ξ
    rw [fourier_eq_paperFT_neg_two_pi_mul, fourier_eq_paperFT_neg_two_pi_mul,
      paperFT_twoBump hb_cont hb_cs]
    push_cast
    ring_nf
  have hnorm_fac : ‖cexp (-(Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))) +
      (-1 : ℂ) * cexp (Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))‖ ≤ 2 := by
    have h1 : ‖cexp (-(Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2)))‖ = 1 := by
      have : -(Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2)) =
          ((Real.pi * ξ * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have h2 : ‖(-1 : ℂ) * cexp (Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))‖ = 1 := by
      have : Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2) =
          ((-(Real.pi * ξ * v) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [norm_mul, norm_neg, norm_one, one_mul, this, Complex.norm_exp_ofReal_mul_I]
    exact (norm_add_le _ _).trans (by linarith)
  have hsq : ‖𝓕 (polarFreeTwoBumpSource hw hv : ℝ → ℂ) ξ‖ ^ 2 ≤
      4 * ‖𝓕 (polarFreeBaseSource hw : ℝ → ℂ) ξ‖ ^ 2 := by
    rw [hft, norm_mul, mul_pow]
    have hf4 : ‖cexp (-(Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))) +
        (-1 : ℂ) * cexp (Complex.I * (-(2 * Real.pi * ξ) : ℂ) * (v / 2))‖ ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hnorm_fac 2
      linarith
    exact mul_le_mul_of_nonneg_right hf4 (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hsq (ccmArchimedeanFormWeight_pos ξ).le).trans_eq (by ring)

/-- Any polar-constrained form-domain lower rate `σ` bounds `zetaZeroWidth` from above. -/
theorem zetaZeroWidth_le_of_mem_polarFormGroundEnergyRates {σ : ℝ}
    (hσ_mem : σ ∈ polarFormGroundEnergyRates) :
    zetaZeroWidth ≤ σ := by
  obtain ⟨hσ, C, A₀, hfloor⟩ := hσ_mem
  have hexists_good : ∃ w : ℝ, 0 < w ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := by
    let bad : Set ℝ := {w : ℝ | 0 < w ∧ ∃ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 ∧
      paperFT (scaledBump w) (gammaOf ρ) = 0}
    have hne : (Ioo (0 : ℝ) 1 \ bad).Nonempty := by
      by_contra hempty
      have hsub : Ioo (0 : ℝ) 1 ⊆ bad := fun x hx => by
        by_contra hnb
        exact hempty ⟨x, hx, hnb⟩
      have hvol : volume (Ioo (0 : ℝ) 1) = 0 :=
        measure_mono_null hsub ((countable_bad_widths zetaZeroConfig).measure_zero volume)
      rw [Real.volume_Ioo] at hvol
      have : (1 : ℝ) - 0 ≤ 0 := ENNReal.ofReal_eq_zero.mp hvol
      linarith
    obtain ⟨w, hw_mem, hw_not_bad⟩ := hne
    exact ⟨w, hw_mem.1, fun ρ hρ hre h0 => hw_not_bad ⟨hw_mem.1, ρ, hρ, hre, h0⟩⟩
  obtain ⟨w, hw0, hgood⟩ := hexists_good
  rw [zetaZeroWidth_le_iff_re_le hσ]
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  rw [re_le_iff_polarFree_lag_twoBump_ge_neg_exp _ temperedConfig_zetaZeroConfig hlt hw0 hgood hσ]
  let B₀ : ℝ := ‖(polarFreeBaseSource hw0).toCCMFormVector‖ ^ 2
  have hB₀_nn : 0 ≤ B₀ := sq_nonneg _
  refine ⟨4 * B₀ * max C 0 * Real.exp (2 * σ * (w + 1)), max 0 (2 * (A₀ - w - 1)), fun v hv => ?_⟩
  have hv0 : 0 ≤ v := (le_max_left 0 _).trans hv
  have hvA₀ : A₀ ≤ v / 2 + w + 1 := by linarith [le_max_right 0 (2 * (A₀ - w - 1))]
  let u_v := polarFreeTwoBumpSource hw0 hv0
  have hb_cont : Continuous (scaledBumpPolarFree w 0) :=
    (contDiff_top_scaledBumpPolarFree w 0).continuous
  have hb_cs : HasCompactSupport (scaledBumpPolarFree w 0) :=
    hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw0 0)
  obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half hw0 0
  have hpol : IsPolarConstrained ⟨v / 2 + w + 1, by linarith⟩ u_v.toCCMFormVector :=
    isPolarConstrained_of_paperFT_half_I_eq_zero u_v
      (paperFT_twoBump_eq_zero hb_cont hb_cs v (-1) hp)
      (paperFT_twoBump_eq_zero hb_cont hb_cs v (-1) hn)
  have hQ_eq : ccmRestrictedWeilSourceQuadratic ⟨v / 2 + w + 1, by linarith⟩ u_v.toCCMFormVector =
      (zetaZeroConfig.W (twoBump (scaledBumpPolarFree w 0) v (-1))
        (twoBump (scaledBumpPolarFree w 0) v (-1))).re :=
    ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil u_v
  have hfl := hfloor ⟨v / 2 + w + 1, by linarith⟩ hvA₀ u_v.toCCMFormVector hpol
  rw [hQ_eq] at hfl
  have hnorm_v : ‖u_v.toCCMFormVector‖ ^ 2 ≤ 4 * B₀ := norm_sq_polarFreeTwoBumpSource_le hw0 hv0
  have hexp_eq : Real.exp (2 * σ * (v / 2 + w + 1)) =
      Real.exp (2 * σ * (w + 1)) * Real.exp (σ * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have hCe : C * Real.exp (2 * σ * (v / 2 + w + 1)) * ‖u_v.toCCMFormVector‖ ^ 2 ≤
      4 * B₀ * max C 0 * Real.exp (2 * σ * (w + 1)) * Real.exp (σ * v) := by
    calc C * Real.exp (2 * σ * (v / 2 + w + 1)) * ‖u_v.toCCMFormVector‖ ^ 2
        ≤ max C 0 * Real.exp (2 * σ * (v / 2 + w + 1)) * ‖u_v.toCCMFormVector‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ max C 0 * Real.exp (2 * σ * (v / 2 + w + 1)) * (4 * B₀) :=
          mul_le_mul_of_nonneg_left hnorm_v
            (mul_nonneg (le_max_right C 0) (Real.exp_pos _).le)
      _ = 4 * B₀ * max C 0 * Real.exp (2 * σ * (w + 1)) * Real.exp (σ * v) := by
          rw [hexp_eq]; ring
  linarith

/-- **Unconditional equality of the polar form-domain ground-energy rate and `zetaZeroWidth`.** -/
theorem polarFormGroundEnergyRate_eq_zetaZeroWidth :
    polarFormGroundEnergyRate = zetaZeroWidth := by
  refine le_antisymm ?_
    (le_csInf polarFormGroundEnergyRates_nonempty fun _ h =>
      zetaZeroWidth_le_of_mem_polarFormGroundEnergyRates h)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact csInf_le bddBelow_polarFormGroundEnergyRates
    (formGroundEnergyRates_subset_polar (birmanSchwingerNormRates_subset_form
      (mem_birmanSchwingerNormRates_of_gt (by linarith))))

/-- **Unconditional equality of the full form-domain ground-energy rate and `zetaZeroWidth`.** -/
theorem formGroundEnergyRate_eq_zetaZeroWidth :
    formGroundEnergyRate = zetaZeroWidth := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le bddBelow_formGroundEnergyRates
      (birmanSchwingerNormRates_subset_form (mem_birmanSchwingerNormRates_of_gt (by linarith)))
  · rw [← polarFormGroundEnergyRate_eq_zetaZeroWidth]
    exact csInf_le_csInf bddBelow_polarFormGroundEnergyRates formGroundEnergyRates_nonempty
      formGroundEnergyRates_subset_polar

/-- **Unconditional equality of the zero-energy Birman–Schwinger operator-norm rate and
`zetaZeroWidth`.** -/
theorem birmanSchwingerNormRate_eq_zetaZeroWidth :
    birmanSchwingerNormRate = zetaZeroWidth := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le bddBelow_birmanSchwingerNormRates
      (mem_birmanSchwingerNormRates_of_gt (by linarith))
  · rw [← formGroundEnergyRate_eq_zetaZeroWidth]
    exact csInf_le_csInf bddBelow_formGroundEnergyRates birmanSchwingerNormRates_nonempty
      birmanSchwingerNormRates_subset_form

/-- **Unconditional equivalence of `RiemannHypothesis` with vanishing of `formGroundEnergyRate`.** -/
theorem riemannHypothesis_iff_formGroundEnergyRate_eq_zero :
    RiemannHypothesis ↔ formGroundEnergyRate = 0 := by
  rw [formGroundEnergyRate_eq_zetaZeroWidth]
  constructor
  · intro hRH
    rw [riemannHypothesis_iff_polarGroundEnergyRate_eq_zero] at hRH
    exact le_antisymm (zetaZeroWidth_le_polarGroundEnergyRate.trans hRH.le) zetaZeroWidth_nonneg
  · intro hw0
    by_contra hnot
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hnot
    have hmem := xiZeroCopy_mem_zetaZeroConfig_carrier q
    have hle := (zetaZeroWidth_le_iff_re_le le_rfl).mp hw0.le (q.1 : ℂ) hmem
    linarith

/-- **Unconditional equivalence of `RiemannHypothesis` with subexponential growth of the zero-energy
Birman–Schwinger operator norm `‖ccmRestrictedWeilFormBirmanSchwinger a 0‖`.** -/
theorem riemannHypothesis_iff_birmanSchwingerNormRate_eq_zero :
    RiemannHypothesis ↔ birmanSchwingerNormRate = 0 := by
  rw [birmanSchwingerNormRate_eq_zetaZeroWidth, ← formGroundEnergyRate_eq_zetaZeroWidth]
  exact riemannHypothesis_iff_formGroundEnergyRate_eq_zero

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
