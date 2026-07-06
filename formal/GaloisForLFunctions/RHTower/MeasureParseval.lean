/-
Parseval's identity for a finite measure against a test function, via the characteristic function.

For a finite measure `μ` on a finite-dimensional inner product space and a continuous test function
`g` with integrable Fourier transform, the `μ`-integral of `g` is recovered as the Fourier-side
pairing of `𝓕 g` with the characteristic function of `μ`:

  ∫ x, g x ∂μ = ∫ w, 𝓕 g w · charFun μ (2π • w).

This is Fubini applied to the Fourier inversion of `g`: writing `g` as the inverse transform of `𝓕 g`
and integrating against `μ`, the `x`-integral of the character is exactly `charFun μ` at the scaled
frequency.  It is the analytic core of the Fourier route to concentration bounds: a majorant `g` of a
ball indicator turns a small-ball probability into a Fourier-side integral controlled by the decay of
`charFun`.
-/
import Mathlib

open MeasureTheory Real Complex
open scoped FourierTransform RealInnerProductSpace

namespace RHTower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [SecondCountableTopology V]

/-- **Parseval for a measure against a test function.**  For a finite measure `μ` and a continuous
`g` whose Fourier transform is integrable, `∫ g dμ` equals the Fourier-side pairing
`∫ w, 𝓕 g w · charFun μ (2π • w)`.  Fourier-invert `g` inside the `μ`-integral and swap with Fubini;
the inner `x`-integral of the character is `charFun μ` at the scaled frequency. -/
theorem integral_measure_eq_integral_fourier_charFun (μ : Measure V) [IsFiniteMeasure μ]
    (g : V → ℂ) (hg : Continuous g) (hgInt : Integrable g) (hFgInt : Integrable (𝓕 g)) :
    ∫ x, g x ∂μ = ∫ w, 𝓕 g w * charFun μ ((2 * π) • w) := by
  have hFgcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hgInt
  have hinv : ∀ x, g x = ∫ w, (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w := by
    intro x
    have h := hgInt.fourierInv_fourier_eq hFgInt (hg.continuousAt (x := x))
    rw [Real.fourierInv_eq] at h
    exact h.symm
  have hcont_unc : Continuous
      (Function.uncurry fun x w => (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w) := by
    apply Continuous.smul
    · exact Real.continuous_fourierChar.comp
        (continuous_inner.comp (continuous_snd.prodMk continuous_fst))
    · exact hFgcont.comp continuous_snd
  have hInt2 : Integrable
      (Function.uncurry fun x w => (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w) (μ.prod volume) := by
    refine Integrable.mono' (hFgInt.norm.comp_snd μ) hcont_unc.aestronglyMeasurable ?_
    filter_upwards with p
    exact le_of_eq (Circle.norm_smul _ _)
  have hstep : ∀ w, ∫ x, (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w ∂μ
      = 𝓕 g w * charFun μ ((2 * π) • w) := by
    intro w
    have hsm : ∀ x, (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w
        = ((Real.fourierChar ⟪w, x⟫ : Circle) : ℂ) * 𝓕 g w := fun x => smul_eq_mul _ _
    calc ∫ x, (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w ∂μ
        = ∫ x, ((Real.fourierChar ⟪w, x⟫ : Circle) : ℂ) * 𝓕 g w ∂μ := by simp_rw [hsm]
      _ = (∫ x, ((Real.fourierChar ⟪w, x⟫ : Circle) : ℂ) ∂μ) * 𝓕 g w := by rw [integral_mul_const]
      _ = 𝓕 g w * ∫ x, ((Real.fourierChar ⟪w, x⟫ : Circle) : ℂ) ∂μ := mul_comm _ _
      _ = 𝓕 g w * charFun μ ((2 * π) • w) := by
          congr 1
          rw [charFun_apply]
          apply integral_congr_ae
          filter_upwards with x
          rw [Real.fourierChar_apply, real_inner_smul_right, real_inner_comm]
  calc ∫ x, g x ∂μ
      = ∫ x, (∫ w, (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w ∂volume) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hinv)
    _ = ∫ w, (∫ x, (Real.fourierChar ⟪w, x⟫ : Circle) • 𝓕 g w ∂μ) ∂volume :=
          integral_integral_swap hInt2
    _ = ∫ w, 𝓕 g w * charFun μ ((2 * π) • w) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall hstep)

/-- **Esseen's concentration inequality (general-majorant form).**  For a probability measure `μ` and
a real test function `g` (with integrable Fourier transform) that majorises the indicator of a
measurable set `A` — `g ≥ 1` on `A` and `g ≥ 0` everywhere — the measure of `A` is bounded by the
`L¹` norm of `𝓕 g`:

  `μ A ≤ ∫ w, ‖𝓕 g w‖`.

Proof: `μ A ≤ ∫ g dμ` by the majorant hypothesis; by Parseval `∫ g dμ = ∫ 𝓕 g · charFun μ (2π·)`,
whose real part is at most its norm, at most `∫ ‖𝓕 g‖ · ‖charFun‖ ≤ ∫ ‖𝓕 g‖` since `‖charFun‖ ≤ 1`.
Choosing `g` a bump of width `t` over a ball turns this into the quadratic small-ball bound the
smooth-packet estimate needs; the Fourier-side integral is then governed by the decay of `charFun`. -/
theorem esseen_concentration (μ : Measure V) [IsProbabilityMeasure μ]
    (g : V → ℂ) (hg : Continuous g)
    (hgVol : Integrable g) (hFgVol : Integrable (𝓕 g)) (hgMu : Integrable g μ)
    (A : Set V) (hA : MeasurableSet A)
    (h1 : ∀ x ∈ A, 1 ≤ (g x).re) (h0 : ∀ x, 0 ≤ (g x).re) :
    (μ A).toReal ≤ ∫ w, ‖𝓕 g w‖ := by
  have hreMu : Integrable (fun x => (g x).re) μ := hgMu.re
  have hstep1 : (μ A).toReal ≤ ∫ x, (g x).re ∂μ := by
    have hind : (μ A).toReal = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [hind]
    apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator hA) hreMu
    filter_upwards with x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]; exact h1 x hx
    · rw [Set.indicator_of_notMem hx]; exact h0 x
  have hstep2 : ∫ x, (g x).re ∂μ = (∫ w, 𝓕 g w * charFun μ ((2 * π) • w)).re := by
    rw [← integral_measure_eq_integral_fourier_charFun μ g hg hgVol hFgVol]
    exact Complex.reCLM.integral_comp_comm hgMu
  have hstep3 : (∫ w, 𝓕 g w * charFun μ ((2 * π) • w)).re ≤ ∫ w, ‖𝓕 g w‖ := by
    calc (∫ w, 𝓕 g w * charFun μ ((2 * π) • w)).re
        ≤ ‖∫ w, 𝓕 g w * charFun μ ((2 * π) • w)‖ := Complex.re_le_norm _
      _ ≤ ∫ w, ‖𝓕 g w * charFun μ ((2 * π) • w)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, ‖𝓕 g w‖ := by
          apply integral_mono_of_nonneg
          · filter_upwards with w; positivity
          · exact hFgVol.norm
          · filter_upwards with w
            rw [norm_mul]
            calc ‖𝓕 g w‖ * ‖charFun μ ((2 * π) • w)‖
                ≤ ‖𝓕 g w‖ * 1 :=
                  mul_le_mul_of_nonneg_left (norm_charFun_le_one _) (norm_nonneg _)
              _ = ‖𝓕 g w‖ := mul_one _
  calc (μ A).toReal ≤ ∫ x, (g x).re ∂μ := hstep1
    _ = (∫ w, 𝓕 g w * charFun μ ((2 * π) • w)).re := hstep2
    _ ≤ ∫ w, ‖𝓕 g w‖ := hstep3

end RHTower
