import GaloisForLFunctions.RHTower.DirichletLShiftData
import GaloisForLFunctions.RHTower.TwistedMobiusMellin
import GaloisForLFunctions.HTGeometry.SmoothWeightPerron

/-!
# The smoothed Perron formula for the twisted Möbius coefficients, on a shifted line

`2π ∑ₙ χ(n)μ(n) w(n) = ∫ (1/L(χ, c+iy)) W(c+iy) dy` for any `c` right of the zero abscissa.

The Perron formula holds on a line of absolute convergence, where the Dirichlet series of `χμ` is
`1/L(χ,·)`; the contour is then pushed left to `c = Θ + δ`, which is legitimate because `1/L` is
holomorphic there and grows slower than any power of the height, while the Mellin transform of the
cutoff decays faster than any power.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- On a line of absolute convergence the Dirichlet series of `χμ` is the reciprocal of the
L-function. -/
theorem tsum_twistedMobius_cpow_eq_inv (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (↗χ * ↗μ) n * (n : ℂ) ^ (-s) = (DirichletCharacter.LFunction χ s)⁻¹ := by
  have hterm : ∀ n : ℕ, (↗χ * ↗μ) n * (n : ℂ) ^ (-s) = LSeries.term (↗χ * ↗μ) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]
  have hsum : ∑' n : ℕ, (↗χ * ↗μ) n * (n : ℂ) ^ (-s) = LSeries (↗χ * ↗μ) s := by
    rw [LSeries]
    exact tsum_congr hterm
  rw [hsum]
  have hone := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hL : DirichletCharacter.LFunction χ s = LSeries ↗χ s :=
    DirichletCharacter.LFunction_eq_LSeries χ hs
  have hne : LSeries ↗χ s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  rw [hL]
  field_simp
  linear_combination hone

/-- **Shifted smoothed Perron formula for the twisted Möbius coefficients.** -/
theorem twistedMobius_perron_shift {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {dl ε : ℝ} (hdl : 0 < dl) (hdl1 : dl < 1) (hε : 0 < ε) {Nw H : ℝ}
    (hN : 0 < Nw) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) (hcd : zeroAbscissa χ + dl ≤ σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, (↗χ * ↗μ) n * ((smoothWeight Nw H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (DirichletCharacter.LFunction χ
            (((zeroAbscissa χ + dl : ℝ) : ℂ) + (y : ℝ) * I))⁻¹ *
          mellin (fun x : ℝ => ((smoothWeight Nw H x : ℝ) : ℂ))
            (((zeroAbscissa χ + dl : ℝ) : ℂ) + (y : ℝ) * I) := by
  obtain ⟨Kb, hKb, hFdiff, hFbd⟩ := exists_shift_data hχ hprim hdl hdl1 hε σ
  have hc0 : (0 : ℝ) < zeroAbscissa χ + dl := by
    have := half_le_zeroAbscissa hχ hprim
    linarith
  have hperron := tsum_mul_smoothWeight_eq_integral (a := ↗χ * ↗μ)
    (norm_twistedMobiusCoeff_le_one χ) (by simp) hN hH hσ
  rw [hperron]
  have hline : ∀ y : ℝ,
      (∑' n : ℕ, (↗χ * ↗μ) n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I))) *
          mellin (fun x : ℝ => ((smoothWeight Nw H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)
        = (DirichletCharacter.LFunction χ ((σ : ℂ) + (y : ℝ) * I))⁻¹ *
          mellin (fun x : ℝ => ((smoothWeight Nw H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) := by
    intro y
    rw [tsum_twistedMobius_cpow_eq_inv χ (by simpa using hσ)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hline)]
  exact integral_mul_mellin_smoothWeight_shift hN hH hc0 hcd hFdiff hKb hε.le hFbd

end RHTower
