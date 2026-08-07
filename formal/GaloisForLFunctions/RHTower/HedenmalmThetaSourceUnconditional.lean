import GaloisForLFunctions.RHTower.HedenmalmHilbertSchmidtNorm
import GaloisForLFunctions.RHTower.HedenmalmIntervalAnomaly
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCurvatureFlow
import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic

/-!
# The theta-cusp source as a positive density source

The whole quantile layer is developed for an abstract positive density source.  This module
supplies the actual arithmetic instance: the all-integer theta-cusp state

`k(x) = ∑_{n ≥ 1} e^{x/2} (4π² n⁴ e^{4x} - 6π n² e^{2x}) e^{-π n² e^{2x}}`

is continuous, everywhere strictly positive, and integrable, so it is a positive density source.
Its completed transform is the completed Riemann function `Ξ_C` on the strip `|Im z| < 1`, and the
tail condition of the quantile layer holds exactly there.

Every theorem of the quantile layer therefore specializes to a statement about the Riemann source
carrying no hypothesis on the source at all.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmHilbertSchmidt

/-! ### Global positivity -/

/-- **The theta-cusp source is everywhere strictly positive.**  Positivity on the positive
half-line is termwise; the negative half-line follows from the reflection law, and the seam point
is the separate cold-seam computation. -/
theorem thetaCuspFullSource_pos (x : ℝ) : 0 < thetaCuspFullSource x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : 0 < -x := by linarith
    have h := thetaCuspFullSource_pos_of_pos hy
    rwa [thetaCuspFullSource_neg x] at h
  · rw [hx]
    exact thetaCuspFullSource_zero_pos_for_cold_seam
  · exact thetaCuspFullSource_pos_of_pos hx

/-! ### The instance -/

/-- **The Hedenmalm theta source.**  The all-integer theta-cusp state as a positive density
source. -/
def thetaSource : PositiveDensitySource where
  k := thetaCuspFullSource
  continuous_k := contDiff_thetaCuspFullSource.continuous
  pos_k := thetaCuspFullSource_pos
  integrable_k := by
    refine (thetaCuspSchwartzReal.integrable (μ := (volume : Measure ℝ))).congr ?_
    filter_upwards with x
    exact thetaCuspSchwartzReal_apply x

@[simp] theorem thetaSource_k (x : ℝ) : thetaSource.k x = thetaCuspFullSource x := rfl

/-- **The theta source is even.** -/
theorem thetaSource_even (x : ℝ) : thetaSource.k (-x) = thetaSource.k x :=
  thetaCuspFullSource_neg x

/-! ### The exact strip of convergence -/

theorem thetaCuspDerivativeExpConstant_nonneg (m : ℕ) :
    0 ≤ thetaCuspDerivativeExpConstant m := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs m 0
  have hexp : Real.exp (-|(0 : ℝ)|) = 1 := by simp
  rw [hexp, mul_one] at h
  exact le_trans (abs_nonneg _) h

/-- **Exponential decay of the theta source.** -/
theorem abs_thetaCuspFullSource_le (x : ℝ) :
    |thetaCuspFullSource x| ≤ thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|) := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 x
  rwa [iteratedDeriv_zero] at h

/-- **The tail condition of the quantile layer holds on the whole strip `|Im z| < 1`.** -/
theorem hasShiftedTail_thetaSource {z : ℂ} (hz : |z.im| < 1) : HasShiftedTail thetaSource z := by
  have hcpos : 0 < 1 - |z.im| := by linarith
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs hcpos).const_mul (thetaCuspDerivativeExpConstant 0)) ?_ ?_
  · refine (contDiff_thetaCuspFullSource.continuous.mul ?_).aestronglyMeasurable
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  · filter_upwards with x
    have hbound := abs_thetaCuspFullSource_le x
    have hkey : Real.exp (-z.im * x) ≤ Real.exp (|z.im| * |x|) := by
      refine Real.exp_le_exp.mpr ?_
      calc -z.im * x ≤ |(-z.im) * x| := le_abs_self _
        _ = |z.im| * |x| := by rw [abs_mul, abs_neg]
    have hCnn := thetaCuspDerivativeExpConstant_nonneg 0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |thetaCuspFullSource x| * Real.exp (-z.im * x)
        ≤ (thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|)) * Real.exp (|z.im| * |x|) := by
          gcongr
      _ = thetaCuspDerivativeExpConstant 0 * Real.exp (-((1 - |z.im|) * |x|)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-! ### The completed transform is the completed Riemann function -/

/-- **The source transform of the theta source is `Ξ_C`** on the strip `|Im z| < 1`. -/
theorem xiC_thetaSource {z : ℂ} (hz : |z.im| < 1) : xiC thetaSource z = XiC z := by
  have hstrip : (-z) ∈ thetaCuspFourierLaplaceStrip := by
    have := abs_lt.mp hz
    exact ⟨by simpa using by linarith [this.2], by simpa using by linarith [this.1]⟩
  have hFL := thetaCuspFourierLaplace_eq_XiC_on_strip hstrip
  have hrw : xiC thetaSource z = thetaCuspFourierLaplace (-z) := by
    rw [xiC, thetaCuspFourierLaplace]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [thetaCuspFourierLaplaceIntegrand, sourceChar, thetaSource_k]
    rw [mul_comm]
    congr 2
    ring
  rw [hrw, hFL, XiC_even]

end HedenmalmThetaSource

end

end RHTower
