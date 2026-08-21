import GaloisForLFunctions.RHTower.ChenGuptaLiSchwartzFourier

open scoped FourierTransform

noncomputable section

namespace RHTower

/-- Certified form of CGL's fixed smooth cutoff: supported on `[1,2]` and equal to one on
`[6/5,9/5]`. Regularity and support are data, never caller-supplied propositions. -/
structure CGLSmoothBump where
  value : ℝ → ℂ
  compactSupport : HasCompactSupport value
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) value
  outside_support : ∀ x, x ∉ Set.Icc (1 : ℝ) 2 → value x = 0
  plateau : ∀ x, x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5) → value x = 1

/-- The CGL cutoff, viewed as a Schwartz function by its proved compact support and smoothness. -/
def CGLSmoothBump.toSchwartz (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  w.compactSupport.toSchwartzMap w.smooth

@[simp] theorem CGLSmoothBump.toSchwartz_apply (w : CGLSmoothBump) (x : ℝ) :
    w.toSchwartz x = w.value x := rfl

/-- Closed Fourier decay for CGL's certified cutoff. -/
theorem cglSmoothBump_abs_pow_mul_norm_fourier_le
    (w : CGLSmoothBump) (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 (w.value) ξ‖ ≤ cglSchwartzFourierDecayBudget w.toSchwartz j := by
  change |ξ| ^ j * ‖𝓕 (w.toSchwartz : ℝ → ℂ) ξ‖ ≤
    cglSchwartzFourierDecayBudget w.toSchwartz j
  exact cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget w.toSchwartz j ξ

/-- Closed unit-lattice Poisson summation for CGL's certified cutoff. -/
theorem cglSmoothBump_tsum_eq_tsum_fourier (w : CGLSmoothBump) (x : ℝ) :
    ∑' n : ℤ, w.value (x + n) =
      ∑' n : ℤ, 𝓕 w.value n * fourier n (x : UnitAddCircle) := by
  change ∑' n : ℤ, w.toSchwartz (x + n) =
    ∑' n : ℤ, 𝓕 (w.toSchwartz : ℝ → ℂ) n * fourier n (x : UnitAddCircle)
  exact cglSchwartz_tsum_eq_tsum_fourier w.toSchwartz x

end RHTower
