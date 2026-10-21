import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.QuasiRHDilationCovarianceAbscissa

/-!
# Lag grids and transport laws read the zero width

Two more obstructions are readings of the zero width `zetaZeroWidth = sup |Re ρ − ½|`.

* **Lag grids and the quantifier gap.** A geometric progression of dyadic prime windows
  `X_k = e^{kℓ}` reads the width exactly up to the attainment of the top: for all but countably
  many widths `w` and steps `ℓ`, `zetaZeroWidth ≤ σ` iff the grid functional is `≥ −Ce^{σkℓ}` for
  all large `k` and every zero above `½ + σ` forces the real parts of the zeros to attain their
  supremum (`zetaZeroWidth_le_iff_attainedTop_and_grid_primeWindow_ge_neg_exp`). What a discrete
  probe loses against the continuum family is exactly the unattained tops.
* **Transport of the Möbius–divisor source.** The signed dilation covariance prefix of the
  Möbius–divisor Abel source is subpower at exponent `1 + 2σ` iff `zetaZeroWidth ≤ σ`
  (`zetaZeroWidth_le_iff_mobiusDivisorDilationCovariancePrefix_subpower`): the exponent of any power
  saving on a non-oscillating zero detector is the width.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### 1. Lag grids read the width up to attainment -/

/-- **Lag grids measure the zero width up to the attainment of the top.** For all but countably
many widths `w ∈ (0, ½ log 2)` and steps `ℓ > 0`, every `σ ≥ 0` and every `N`: `zetaZeroWidth ≤ σ`
iff (a zero above `½ + σ` forces an attained maximum of `Re ρ`) and the dyadic prime windows at
`X_k = e^{kℓ}` are `≥ −Ce^{σkℓ}` for `k ≥ N`. -/
theorem zetaZeroWidth_le_iff_attainedTop_and_grid_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∃ E' : Set ℝ, E'.Countable ∧ ∀ w : ℝ, 0 < w →
      2 * w < Real.log 2 → w ∉ E → ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ E' → ∀ σ : ℝ, 0 ≤ σ → ∀ N : ℕ,
        (zetaZeroWidth ≤ σ ↔
          ((∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 + σ < ρ.re) →
              ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ ρ₀.re) ∧
            ∃ C : ℝ, ∀ k : ℕ, N ≤ k → -(C * Real.exp (σ * (k * ℓ))) ≤
              (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
                (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, _, countable_resonantSteps zetaZeroConfig,
    fun w hw hw2 hwE ℓ hℓ hres σ hσ N => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have heq : ∀ k : ℕ, (zetaZeroConfig.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re =
      (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re := fun k => by
    have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) (k * ℓ) (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]
  rw [zetaZeroWidth_le_iff_re_le hσ,
    re_le_iff_topAttained_above_and_grid_lag_ge_neg_exp _ temperedConfig_zetaZeroConfig hw
      hgood hℓ hres hσ N]
  simp_rw [heq]

/-! ### 2. The transport law of the Möbius–divisor source reads the width -/

/-- **The signed dilation covariance prefix is subpower at exponent `1 + 2σ` iff the width is at
most `σ`.** -/
theorem zetaZeroWidth_le_iff_mobiusDivisorDilationCovariancePrefix_subpower {φ σ : ℝ}
    (hφ : 1 / 2 ≤ φ) (hσ : φ ≤ 1 / 2 + σ) :
    zetaZeroWidth ≤ σ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      mobiusDivisorDilationCovariancePrefix φ N ≤ C * (N : ℝ) ^ (2 * (1 / 2 + σ) + ε) :=
  (zetaZeroWidth_le_iff_zetaZeroAbscissa_le (by linarith)).trans
    (zetaZeroAbscissa_le_iff_mobiusDivisorDilationCovariancePrefix_subpower hφ hσ)

end GaloisForLFunctions.SquareRootThreshold
