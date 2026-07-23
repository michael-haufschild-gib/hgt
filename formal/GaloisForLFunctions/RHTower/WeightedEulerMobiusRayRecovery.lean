import GaloisForLFunctions.RHTower.WeightedEulerMobiusDecayTransfer
import GaloisForLFunctions.RHTower.LambertRayRecovery
import GaloisForLFunctions.RHTower.CompactCarrierLambert

/-!
# Quantitative Möbius recovery along a multiplicative ray

The decay companion of `fourierBorel_eq_zero_of_lambert_ray_zero`: if a
function decays geometrically along the multiplicative ray `{n·x}` and its
positive Lambert derivative is exponentially small there (`≤ D·ρⁿ`,
`ρ ≤ 1/2`), then Möbius inversion bounds the first ray value:

`‖F x‖ ≤ 4·D·ρ`.

Composed with `positiveLambertDerivative_compactFourierBorel`, this converts
sampled decay of the compact-carrier Lambert transform into decay of the
Fourier–Borel transform itself — the step from the oversampled sampling bound
to the carrier-separation hypothesis.
-/

noncomputable section

namespace RHTower

/-- **Quantitative Möbius ray recovery**: geometric ray decay of `F` plus
exponential smallness of its positive Lambert derivative bound the first ray
value with the explicit constant `4`. -/
theorem norm_fourierBorel_le_of_lambert_ray_decay
    (F : ℂ → ℂ) (x : ℂ) {C r D ρ : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ n : ℕ+, ‖F ((n : ℂ) * x)‖ ≤ C * r ^ (n : ℕ))
    (hD : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hH : ∀ n : ℕ+,
      ‖positiveLambertDerivative F ((n : ℂ) * x)‖ ≤ D * ρ ^ (n : ℕ)) :
    ‖F x‖ ≤ 4 * D * ρ := by
  have h := norm_first_le_of_weightedLambert_decay
    (fun n : ℕ+ => F ((n : ℂ) * x)) hC hr0 hr1 hdecay hD hρ0 hρhalf
    (fun n => by
      rw [weightedLambertTransform_ray_eq]
      exact hH n)
  simpa using h

/-- The compact-carrier form: sampled decay of the Lambert transform along
the ray `{n·x}` bounds the Fourier–Borel transform at `x`. -/
theorem norm_compactFourierBorel_le_of_sampled_lambert_decay
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (x : ℂ)
    (hq : ∀ n : ℕ+, ‖compactExponentialTest s ((n : ℂ) * x)‖ < 1)
    {C r D ρ : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ n : ℕ+,
      ‖compactFourierBorel L s ((n : ℂ) * x)‖ ≤ C * r ^ (n : ℕ))
    (hD : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hlam : ∀ n : ℕ+,
      ‖compactCarrierLambertTransform L s ((n : ℂ) * x)‖ ≤ D * ρ ^ (n : ℕ)) :
    ‖compactFourierBorel L s x‖ ≤ 4 * D * ρ := by
  apply norm_fourierBorel_le_of_lambert_ray_decay
    (compactFourierBorel L s) x hC hr0 hr1 hdecay hD hρ0 hρhalf
  intro n
  rw [positiveLambertDerivative_compactFourierBorel L s _ (hq n)]
  exact hlam n

end RHTower
