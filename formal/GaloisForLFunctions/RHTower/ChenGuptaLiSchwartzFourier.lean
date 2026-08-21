import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCubicDiagonal
import Mathlib.Analysis.Fourier.PoissonSummation

open scoped FourierTransform
open MeasureTheory

noncomputable section

namespace RHTower

/-- Explicit derivative-integral budget controlling the Fourier decay of a Schwartz function. -/
def cglSchwartzFourierDecayBudget (f : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * ∑ p ∈ Finset.range 1 ×ˢ Finset.range (j + 1),
    ∫ x : ℝ, |x| ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖

/-- Repeated integration by parts gives a closed Fourier-decay bound for every Schwartz input. -/
theorem cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget
    (f : SchwartzMap ℝ ℂ) (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 (f : ℝ → ℂ) ξ‖ ≤ cglSchwartzFourierDecayBudget f j := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤)
    (f := (f : ℝ → ℂ)) (f.smooth ⊤)
    (fun k n _hk _hn => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k n)
    (k := 0) (n := j) le_top le_top ξ
  simpa [cglSchwartzFourierDecayBudget, Real.norm_eq_abs, norm_iteratedFDeriv_zero] using h

/-- The unit-lattice Poisson identity available for every CGL Schwartz input. -/
theorem cglSchwartz_tsum_eq_tsum_fourier (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f x

end RHTower
