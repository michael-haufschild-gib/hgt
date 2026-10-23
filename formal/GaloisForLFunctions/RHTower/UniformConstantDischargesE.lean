import GaloisForLFunctions.RHTower.DlvpSharp
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.WeilFullConeNearNullPositiveDefinite

set_option autoImplicit false

/-!
# Pole and smooth-transition constants supplied to three conditional estimates

* The de la Vallée Poussin inequalities `dlvp_sharp` and `dlvp_half` take a pole bound
  `Re(-ζ'/ζ)(u) ≤ 1/(u - 1) + A` on `(1, 2]`; `neg_re_logDeriv_riemannZeta_real_le` proves it with
  `A = 1`, so both hold with the explicit constants `dlvpSharpConstant 1`, `dlvpHalfConstant 1`.
* The Weil-form bound `norm_W_shiftComb_le` takes a bound on `deriv Real.smoothTransition`; the
  constant does not enter its conclusion, so `exists_bound_deriv_smoothTransition` removes it.
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

/-- Sharp de la Vallée Poussin inequality with the explicit pole constant `A = 1`. -/
theorem dlvp_sharp_explicit {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (q₀ : XiZeroCopy)
    (hγ : 4 ≤ (q₀.1 : ℂ).im) :
    4 / (σ - (q₀.1 : ℂ).re) ≤
      3 / (σ - 1) + 5 * Real.log ((q₀.1 : ℂ).im) + dlvpSharpConstant 1 :=
  dlvp_sharp (fun _ h1 h2 => neg_re_logDeriv_riemannZeta_real_le h1 h2) hσ1 hσ2 q₀ hγ

/-- Half-logarithm de la Vallée Poussin inequality with the explicit pole constant `A = 1`. -/
theorem dlvp_half_explicit {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (q₀ : XiZeroCopy)
    (hγ : 4 ≤ (q₀.1 : ℂ).im) :
    4 / (σ - (q₀.1 : ℂ).re) ≤
      3 / (σ - 1) + 5 / 2 * Real.log ((q₀.1 : ℂ).im) + dlvpHalfConstant 1 :=
  dlvp_half (fun _ h1 h2 => neg_re_logDeriv_riemannZeta_real_le h1 h2) hσ1 hσ2 q₀ hγ

namespace WeilExcess

/-- The zero-side Weil form of a shifted combination of truncated kernels is bounded by its
`e^{|x|/2}`-weighted coefficient mass times the truncated tail energy. -/
theorem norm_W_shiftComb_le_unconditional {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (L : ℝ) :
    ‖zetaZeroConfig.W (shiftComb s c x L) (shiftComb s c x L)‖ ≤
      (∑ j ∈ s, |c j| * Real.exp (|x j| / 2)) ^ 2 *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  obtain ⟨Λ, -, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  exact norm_W_shiftComb_le s c x L hΛ

end WeilExcess

end RHTower
