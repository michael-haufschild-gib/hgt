import GaloisForLFunctions.RHTower.ConnesOscillatingQuotient

/-!
# The truncated sign pairing against the oscillating quotient

Step 1b (continued) of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Substituting the truncated kernel `2i(1 − cos 2πXu)/(2πu)` of `ConnesSgnFourierKernel` into the
Fubini pairing of `ConnesSgnFubiniPairing` gives

  `∫_{-X}^{X} sgn(x) g(x) dx = (i/π) ∫ 𝓕g(u) · (1 − cos 2πXu)/u du`.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap FourierTransform Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Almost every real number is nonzero. -/
theorem connes_ae_ne_zero : ∀ᵐ u : ℝ, u ≠ 0 := by
  have h0 : (volume : Measure ℝ) {(0 : ℝ)} = 0 := Real.volume_singleton
  filter_upwards [compl_mem_ae_iff.2 h0] with u hu
  simpa using hu

/-- **The truncated sign pairing against the oscillating quotient.** -/
theorem connes_sgn_pairing_osc (g : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 ≤ X) :
    (∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * g x)
      = (Complex.I / (Real.pi : ℂ)) *
          ∫ u : ℝ, (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
            * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ) := by
  rw [connes_sgn_pairing_truncated g hX, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [connes_ae_ne_zero] with u hu
  show (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
      * (∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * connesSpaceChar u x)
    = Complex.I / (Real.pi : ℂ) * ((𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
      * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ))
  rw [connes_sgn_truncated_kernel hu hX]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hu' : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  push_cast
  field_simp

end

end GaloisForLFunctions.RHTower
