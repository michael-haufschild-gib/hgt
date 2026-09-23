import GaloisForLFunctions.RHTower.L2FourierUncertainty
import GaloisForLFunctions.RHTower.BandUncertainty

/-!
# Closed Fourier indeterminacy no-go laws

The corpus Fourier uncertainty theorems are recast as unconditional nonexistence statements.
They exclude simultaneous localization, an open spectral gap for bounded-support data, and an
interior band signal with zero Fourier tail.
-/

namespace RHTower

open MeasureTheory Set FourierTransform
open scoped FourierTransform

/-- No nonzero integrable function and its Fourier integral both have bounded essential support. -/
theorem no_nonzero_integrable_bicompact_fourier_pair :
    ¬ ∃ (f : ℝ → ℂ) (a b : ℝ),
      Integrable f ∧
        (∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) ∧
        (∀ᵐ w ∂volume,
          w ∉ Icc (-b) b → FourierTransform.fourier f w = 0) ∧
        ¬ f =ᵐ[volume] 0 := by
  rintro ⟨f, a, b, hf, hs, hF, hne⟩
  exact hne (integrable_fourier_uncertainty hf hs hF)

/-- No nonzero `L²` function and its unitary Fourier transform both have bounded support. -/
theorem no_nonzero_l2_bicompact_fourier_pair :
    ¬ ∃ (f : Lp ℂ 2 (volume : Measure ℝ)) (a b : ℝ),
      f ≠ 0 ∧
        (∀ᵐ x ∂volume, x ∉ Icc (-a) a → (f : ℝ → ℂ) x = 0) ∧
        (∀ᵐ w ∂volume, w ∉ Icc (-b) b →
          (((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = 0)) := by
  rintro ⟨f, a, b, hne, hs, hF⟩
  exact hne (l2_fourier_uncertainty f hs hF)

/-- A bounded-support nonzero `L²` function cannot have even one nonempty open Fourier gap. -/
theorem no_nonzero_bounded_l2_with_fourier_spectral_gap :
    ¬ ∃ (f : Lp ℂ 2 (volume : Measure ℝ)) (a c d : ℝ),
      f ≠ 0 ∧ c < d ∧
        (∀ᵐ x ∂volume, x ∉ Icc (-a) a → (f : ℝ → ℂ) x = 0) ∧
        (∀ᵐ w ∂volume, w ∈ Ioo c d →
          (((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = 0)) := by
  rintro ⟨f, a, c, d, hne, hcd, hs, hF⟩
  exact hne (l2_eq_zero_of_bounded_support_fourier_vanishes_on_Ioo f hs hcd hF)

end RHTower

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set FourierTransform
open scoped FourierTransform

/-- A continuous band test cannot be nonzero at an interior point while its spectral tail is zero. -/
theorem no_band_interior_signal_with_zero_spectral_tail :
    ¬ ∃ (c : ℝ) (Φ : ℝ → ℝ) (x : ℝ),
      0 < c ∧ Continuous Φ ∧ x ∈ Ioo (-1 : ℝ) 1 ∧ Φ x ≠ 0 ∧
        (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
          ‖𝓕 (bandTrunc Φ) ξ‖ ^ (2 : ℕ)) = 0 := by
  rintro ⟨c, Φ, x, hc, hΦ, hx, hne, htail⟩
  exact hne (eqOn_zero_of_spectral_tail_eq_zero hc hΦ htail x hx)

end GaloisForLFunctions.RHTower
