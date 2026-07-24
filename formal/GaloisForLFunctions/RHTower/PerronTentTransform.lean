import GaloisForLFunctions.RHTower.PerronLaplaceKernel
import Mathlib.Analysis.Fourier.Inversion

/-!
# The Fourier transform of the Perron tent

`𝓕(u·e^{-au}·1_{u>0})(w) = (a + 2πiw)⁻²` for `a > 0` — the Laplace
kernel integral read as a Fourier transform.  Together with the
integrability of both sides this feeds Fourier inversion, which
evaluates the smoothed Perron kernel
`(1/2πi)∫_{(a)} y^s/s² ds = (log y)⁺`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter

/-- The one-sided tent `u·e^{-au}·1_{u>0}`. -/
def perronTent (a : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Ioi 0)
    (fun u : ℝ => (u : ℂ) * Complex.exp (-((a : ℂ) * u)))

/-- The tent is integrable. -/
theorem integrable_perronTent {a : ℝ} (ha : 0 < a) :
    Integrable (perronTent a) := by
  rw [perronTent, integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_mul_exp_neg_mul
    (by rwa [Complex.ofReal_re] : 0 < ((a : ℝ) : ℂ).re)

/-- The tent is continuous (the jump at `0` has height `0`). -/
theorem continuous_perronTent (a : ℝ) : Continuous (perronTent a) := by
  rw [perronTent]
  rw [continuous_iff_continuousAt]
  intro v
  rcases lt_trichotomy v 0 with hv | hv | hv
  · apply ContinuousAt.congr_of_eventuallyEq continuousAt_const
    filter_upwards [Iio_mem_nhds hv] with u hu
    rw [Set.indicator_of_notMem (by simpa using le_of_lt hu)]
  · subst hv
    have hbound : ∀ u : ℝ,
        ‖Set.indicator (Set.Ioi 0)
          (fun u : ℝ => (u : ℂ) * Complex.exp (-((a : ℝ) * u : ℂ))) u‖
          ≤ |u| * Real.exp (|a| * |u|) := by
      intro u
      by_cases hu : u ∈ Set.Ioi 0
      · rw [Set.indicator_of_mem hu, norm_mul, Complex.norm_exp,
          Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
        apply Real.exp_le_exp.2
        have h1 : (-((a : ℝ) * u : ℂ)).re = -(a * u) := by
          simp [Complex.mul_re]
        rw [h1]
        calc -(a * u) ≤ |a * u| := neg_le_abs _
          _ = |a| * |u| := abs_mul a u
      · rw [Set.indicator_of_notMem hu]
        simp
        positivity
    -- squeeze to `0 = value at 0`
    have hval0 : Set.indicator (Set.Ioi 0)
        (fun u : ℝ => (u : ℂ) * Complex.exp (-((a : ℝ) * u : ℂ))) 0 = 0 := by
      rw [Set.indicator_of_notMem (by simp)]
    rw [ContinuousAt, hval0]
    apply squeeze_zero_norm hbound
    have h1 : Tendsto (fun u : ℝ => |u| * Real.exp (|a| * |u|))
        (nhds 0) (nhds (|0| * Real.exp (|a| * |0|))) := by
      apply Tendsto.mul
      · exact (continuous_abs.tendsto 0)
      · exact (Real.continuous_exp.comp
          (continuous_const.mul continuous_abs)).tendsto 0
    simpa using h1
  · apply ContinuousAt.congr_of_eventuallyEq
      (f := fun u : ℝ => (u : ℂ) * Complex.exp (-((a : ℝ) * u : ℂ)))
    · fun_prop
    · filter_upwards [Ioi_mem_nhds hv] with u hu
      rw [Set.indicator_of_mem (by simpa using hu)]

set_option maxHeartbeats 1600000 in
/-- **The tent transform**: `𝓕(perronTent a)(w) = (a + 2πiw)⁻²`. -/
theorem fourier_perronTent {a : ℝ} (ha : 0 < a) (w : ℝ) :
    FourierTransform.fourier (perronTent a) w
      = 1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 := by
  have hcre : 0 < ((a : ℂ) + 2 * Real.pi * w * Complex.I).re := by
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
    exact ha
  rw [Real.fourier_real_eq]
  have hind : ∀ v : ℝ, (Real.fourierChar (-(v * w)) : ℂ) • perronTent a v
      = Set.indicator (Set.Ioi 0)
          (fun v : ℝ => (v : ℂ) * Complex.exp (-(((a : ℂ)
            + 2 * Real.pi * w * Complex.I) * v))) v := by
    intro v
    rw [perronTent]
    by_cases hv : v ∈ Set.Ioi 0
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul,
        Real.fourierChar_apply]
      rw [show Complex.exp (((2 * Real.pi * -(v * w) : ℝ) : ℂ) * Complex.I)
          * ((v : ℂ) * Complex.exp (-((a : ℂ) * v)))
          = (v : ℂ) * (Complex.exp (((2 * Real.pi * -(v * w) : ℝ) : ℂ)
              * Complex.I) * Complex.exp (-((a : ℂ) * v))) from by ring,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv,
        smul_zero]
  calc ∫ v : ℝ, (Real.fourierChar (-(v * w)) : ℂ) • perronTent a v
      = ∫ v : ℝ, Set.indicator (Set.Ioi 0)
          (fun v : ℝ => (v : ℂ) * Complex.exp (-(((a : ℂ)
            + 2 * Real.pi * w * Complex.I) * v))) v :=
        integral_congr_ae (Filter.Eventually.of_forall hind)
    _ = ∫ v in Set.Ioi (0 : ℝ),
          (v : ℂ) * Complex.exp (-(((a : ℂ)
            + 2 * Real.pi * w * Complex.I) * v)) :=
        integral_indicator measurableSet_Ioi
    _ = 1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 :=
        integral_mul_exp_neg_mul_Ioi hcre

end RHTower
