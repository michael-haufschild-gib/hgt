import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCompactHullParityLaw
import GaloisForLFunctions.HTGeometry.PrimitiveAverageLimit
import GaloisForLFunctions.HTGeometry.ConvolutionKernelSquareBound
import GaloisForLFunctions.RHTower.CCM.CCMUnitaryPolarSourceAtlas
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLargeNegativeShiftCentralFlux
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCesaroCurvatureRecurrence

/-!
# Regularity of Suzuki's screw function and its convolution kernel

Suzuki's screw function of a multiplicity-weighted ordinate family is the explicit series

`g t = ∑ 2 * mult γ / γ ^ (2 : ℕ) * (1 - cos (γ t))`.

Two properties of it are used as inputs elsewhere: that it vanishes at the origin, and that it is
continuous.  Both are consequences of the definition — the first termwise, the second from the
uniform bound `|1 - cos| ≤ 2` against the summable weights — so neither has to be assumed.

With them, two statements about the aperture and the kernel follow at once: the centred aperture
average of `g` tends to zero as the aperture shrinks, and the convolution kernel `g (t - s)` is
square integrable on a square of finite side.  The latter is the Hilbert–Schmidt input for the
operator attached to the kernel.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

variable {G : Type*} {mult : G → ℕ} {gamma : G → ℝ}

/-- Suzuki's screw function vanishes at the origin: every term carries the factor `1 - cos 0`. -/
@[simp] theorem suzukiScrewFunction_zero :
    _root_.RHTower.suzukiScrewFunction mult gamma 0 = 0 := by
  simp [_root_.RHTower.suzukiScrewFunction, screwSeries]

/-- Suzuki's screw function is continuous whenever its weights are summable. -/
theorem continuous_suzukiScrewFunction
    (hsum : Summable (_root_.RHTower.suzukiScrewWeight mult gamma)) :
    Continuous (_root_.RHTower.suzukiScrewFunction mult gamma) :=
  screwSeries_continuous (fun g => _root_.RHTower.suzukiScrewWeight_nonneg g) hsum

/-- **The small-aperture limit for Suzuki's own screw function.**  The centred aperture average
tends to zero as the aperture shrinks, with both hypotheses discharged from the definition. -/
theorem tendsto_suzukiScrewAperture_average_zero
    (hsum : Summable (_root_.RHTower.suzukiScrewWeight mult gamma)) :
    Tendsto
      (fun A : ℝ =>
        (∫ t in (0 : ℝ)..(2 * A), _root_.RHTower.suzukiScrewFunction mult gamma t) / (2 * A))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_primitive_div_two_mul_nhdsGT_zero (continuous_suzukiScrewFunction hsum)
    suzukiScrewFunction_zero

/-- **The Suzuki screw convolution kernel is square integrable on a finite square.**  This is the
Hilbert–Schmidt finiteness input for the operator with kernel `g (t - s)`. -/
theorem integral_integral_sq_suzukiScrewKernel_le
    (hsum : Summable (_root_.RHTower.suzukiScrewWeight mult gamma)) {A : ℝ} (hA : 0 ≤ A) :
    (∫ t in (0 : ℝ)..A, ∫ s in (0 : ℝ)..A,
        (_root_.RHTower.suzukiScrewFunction mult gamma (t - s)) ^ (2 : ℕ))
      ≤ A * ∫ u in (-A)..A, (_root_.RHTower.suzukiScrewFunction mult gamma u) ^ (2 : ℕ) :=
  integral_integral_sq_sub_le (continuous_suzukiScrewFunction hsum) hA

/-! ## The screw function of the actual critical ordinates

The corpus carries the screw series of the critical zero family itself, with weights `1 / γ ^ (2 : ℕ)`
over the critical ordinates, together with unconditional summability of those weights.  Everything
above therefore specialises to it with no hypotheses at all. -/

section XiLine

/-- The screw series of the critical ordinates vanishes at the origin. -/
@[simp] theorem xiLineScrewSeries_zero : _root_.RHTower.xiLineScrewSeries 0 = 0 := by
  simp [_root_.RHTower.xiLineScrewSeries, screwSeries]

/-- **The small-aperture limit for the screw function of the critical ordinates**, with no
hypotheses: summability of the weights `1 / γ ^ (2 : ℕ)` is a corpus theorem. -/
theorem tendsto_xiLineScrewAperture_average_zero :
    Tendsto
      (fun A : ℝ => (∫ t in (0 : ℝ)..(2 * A), _root_.RHTower.xiLineScrewSeries t) / (2 * A))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_primitive_div_two_mul_nhdsGT_zero _root_.RHTower.xiLineScrewSeries_continuous
    xiLineScrewSeries_zero

/-- **The convolution kernel of the critical-ordinate screw function is square integrable on a
finite square**, unconditionally. -/
theorem integral_integral_sq_xiLineScrewKernel_le {A : ℝ} (hA : 0 ≤ A) :
    (∫ t in (0 : ℝ)..A, ∫ s in (0 : ℝ)..A,
        (_root_.RHTower.xiLineScrewSeries (t - s)) ^ (2 : ℕ))
      ≤ A * ∫ u in (-A)..A, (_root_.RHTower.xiLineScrewSeries u) ^ (2 : ℕ) :=
  integral_integral_sq_sub_le _root_.RHTower.xiLineScrewSeries_continuous hA

/-- **Small apertures clear the Xi curvature threshold.**  The threshold is strictly negative while
the aperture average tends to zero, so some positive aperture has its average strictly above the
threshold. -/
theorem exists_aperture_XiC_curvature_lt_xiLineScrewAverage :
    ∃ A : ℝ, 0 < A ∧ (deriv (deriv _root_.RHTower.XiC) 0 / _root_.RHTower.XiC 0).re
      < (∫ t in (0 : ℝ)..(2 * A), _root_.RHTower.xiLineScrewSeries t) / (2 * A) := by
  have hev := (tendsto_order.1 tendsto_xiLineScrewAperture_average_zero).1 _
    _root_.RHTower.XiC_secondDeriv_div_center_re_neg
  have hpos : ∀ᶠ A : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < A :=
    self_mem_nhdsWithin
  obtain ⟨A, hA1, hA2⟩ := (hpos.and hev).exists
  exact ⟨A, hA1, hA2⟩

/-- **Theorem C's conclusion for the actual critical ordinates.**  At some positive aperture, every
sufficiently negative dyadic shift pair puts the normalized intercept strictly above the Xi
curvature threshold, i.e. on the side forbidden by the Herglotz sign.

The hypothesis is exactly the card's step identifying the edge jet's limit with the screw aperture
average; everything else is discharged. -/
theorem exists_aperture_eventually_XiC_curvature_lt_intercept {q : ℝ → ℝ → ℝ}
    (hq : ∀ A : ℝ, Tendsto (q A) atBot
      (𝓝 ((∫ t in (0 : ℝ)..(2 * A), _root_.RHTower.xiLineScrewSeries t) / (2 * A)))) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ L in atTop,
      (deriv (deriv _root_.RHTower.XiC) 0 / _root_.RHTower.XiC 0).re
        < _root_.RHTower.suzukiDyadicNegativeShiftIntercept (q A) L := by
  obtain ⟨A, hApos, hAgt⟩ := exists_aperture_XiC_curvature_lt_xiLineScrewAverage
  exact ⟨A, hApos,
    _root_.RHTower.eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept (hq A) hAgt⟩

/-! ### In the corpus's Cesàro vocabulary

The aperture average above is the corpus's own `suzukiScrewCesaroMean` at aperture `2A`.  Recording
the identification lets these statements compose with the existing Cesàro and crossing machinery
rather than standing as a parallel notion. -/

theorem xiLineScrewAperture_eq_cesaroMean (A : ℝ) :
    (∫ t in (0 : ℝ)..(2 * A), _root_.RHTower.xiLineScrewSeries t) / (2 * A)
      = _root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * A) := rfl

/-- The Cesàro mean of the critical-ordinate screw function vanishes at small aperture. -/
theorem tendsto_cesaroMean_xiLineScrewSeries_zero :
    Tendsto
      (fun A : ℝ =>
        _root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * A))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_xiLineScrewAperture_average_zero

/-- Some positive aperture has Cesàro mean strictly above the Xi curvature threshold. -/
theorem exists_aperture_XiC_curvature_lt_cesaroMean :
    ∃ A : ℝ, 0 < A ∧ (deriv (deriv _root_.RHTower.XiC) 0 / _root_.RHTower.XiC 0).re
      < _root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * A) :=
  exists_aperture_XiC_curvature_lt_xiLineScrewAverage

/-- **Theorem C's conclusion in the corpus's Cesàro vocabulary.**  Stated so that the source
hypothesis reads exactly like the one carried by
`xiSuzukiScrewCesaroCrossing_selects_dyadicCentralFlux`. -/
theorem exists_aperture_eventually_XiC_curvature_lt_intercept_cesaro {q : ℝ → ℝ → ℝ}
    (hq : ∀ A : ℝ, Tendsto (q A) atBot
      (𝓝 (_root_.RHTower.suzukiScrewCesaroMean _root_.RHTower.xiLineScrewSeries (2 * A)))) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ L in atTop,
      (deriv (deriv _root_.RHTower.XiC) 0 / _root_.RHTower.XiC 0).re
        < _root_.RHTower.suzukiDyadicNegativeShiftIntercept (q A) L :=
  exists_aperture_eventually_XiC_curvature_lt_intercept hq

end XiLine

end GaloisForLFunctions.RHTower
