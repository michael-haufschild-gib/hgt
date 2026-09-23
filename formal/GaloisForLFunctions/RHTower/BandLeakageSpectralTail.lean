import GaloisForLFunctions.RHTower.BandFrequencyWindow
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The band leakage of a test function is its spectral tail

Plancherel turns the frequency-window reading of the band quadratic form into an exact formula for the
*leakage* of a test function supported in `[-1, 1]`:

```text
∫_(-1)^(1 : ℕ) psi² - ∫∫ sinc_c(x-y) psi(x) psi(y) = ∫_(|xi| > c/(2 pi)) ‖𝓕 psi (xi)‖² d xi.
```

The left side is the deficit of the Rayleigh quotient of the band operator at `psi`; the right side is
the spectral mass of `psi` outside the band.  Since the largest band eigenvalue is the supremum of that
Rayleigh quotient, every explicit test function turns into an upper bound for the band leakage
`1 - lambda_0(c)`, and the exponential rate of the leakage envelope is exactly the rate at which the
spectral tail of the best test function decays.

The route is: the truncation lies in every `L^p` (bounded, compactly supported), mathlib's `L²`
Fourier transform is an isometry, and the corpus bridge identifies its class with the classical
Fourier integral of the truncation.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-- The band truncation of a continuous function lies in every `L^p` of the line: it is bounded and
supported in a set of finite measure. -/
theorem memLp_bandTrunc {ψ : ℝ → ℝ} (hψ : Continuous ψ) (p : ENNReal) :
    MemLp (bandTrunc ψ) p (volume : Measure ℝ) := by
  rw [bandTrunc, memLp_indicator_iff_restrict measurableSet_Icc]
  haveI hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hψ.continuousOn
  refine MemLp.of_bound ?_ C ?_
  · exact (Complex.continuous_ofReal.comp hψ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Complex.norm_real]
    exact hC x hx

theorem integrable_bandTrunc {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Integrable (bandTrunc ψ) (volume : Measure ℝ) :=
  memLp_one_iff_integrable.mp (memLp_bandTrunc hψ 1)

/-- **Plancherel for the band truncation.**  The total spectral energy of the truncation is its
`L²` energy on the band. -/
theorem integral_norm_sq_fourier_bandTrunc {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ ξ : ℝ, ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2) = ∫ x : ℝ, ‖bandTrunc ψ x‖ ^ 2 :=
  integral_norm_sq_fourier_eq (integrable_bandTrunc hψ) (memLp_bandTrunc hψ 2)

/-- The spectral density of the truncation is integrable. -/
theorem integrable_norm_sq_fourier_bandTrunc {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Integrable (fun ξ : ℝ => ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2) (volume : Measure ℝ) :=
  integrable_norm_sq_fourier (integrable_bandTrunc hψ) (memLp_bandTrunc hψ 2)

/-- The `L²` energy of the truncation is the integral of the square over the band. -/
theorem integral_norm_sq_bandTrunc (ψ : ℝ → ℝ) :
    (∫ x : ℝ, ‖bandTrunc ψ x‖ ^ 2) = ∫ x in (-1 : ℝ)..1, ψ x ^ 2 := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hpt : ∀ x : ℝ, ‖bandTrunc ψ x‖ ^ 2
      = Set.indicator (Set.Icc (-1 : ℝ) 1) (fun x => ψ x ^ 2) x := by
    intro x
    simp only [bandTrunc, Set.indicator_apply]
    split_ifs with hx
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · simp
  calc (∫ x : ℝ, ‖bandTrunc ψ x‖ ^ 2)
      = ∫ x : ℝ, Set.indicator (Set.Icc (-1 : ℝ) 1) (fun x => ψ x ^ 2) x := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x in Set.Icc (-1 : ℝ) 1, ψ x ^ 2 :=
        MeasureTheory.integral_indicator measurableSet_Icc
    _ = ∫ x in (-1 : ℝ)..1, ψ x ^ 2 := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

/-- **The leakage of a test function is its spectral tail.**  The deficit of the band Rayleigh
quotient equals the spectral mass outside the band. -/
theorem leakage_eq_spectral_tail {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ x in (-1 : ℝ)..1, ψ x ^ 2)
        - ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (ψ x * ψ y)
      = ∫ ξ in (Set.Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
          ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2 := by
  have hle : -(c / (2 * Real.pi)) ≤ c / (2 * Real.pi) := by
    have : (0 : ℝ) < c / (2 * Real.pi) := by positivity
    linarith
  -- the total spectral energy splits at the window
  have hintF : Integrable (fun ξ : ℝ => ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2) (volume : Measure ℝ) :=
    integrable_norm_sq_fourier_bandTrunc hψ
  have hsplit := MeasureTheory.integral_add_compl
    (measurableSet_Icc (a := -(c / (2 * Real.pi))) (b := c / (2 * Real.pi))) hintF
  -- the window part is the band quadratic form
  have hwindow : (∫ ξ in Set.Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)),
      ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (ψ x * ψ y) := by
    rw [double_integral_sincKernel_eq_frequency_energy hc hψ,
      intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- and the total is the band energy
  have htotal : (∫ ξ : ℝ, ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2) = ∫ x in (-1 : ℝ)..1, ψ x ^ 2 := by
    rw [integral_norm_sq_fourier_bandTrunc hψ, integral_norm_sq_bandTrunc ψ]
  rw [← htotal, ← hsplit, hwindow]
  ring

end GaloisForLFunctions.RHTower

end
