import GaloisForLFunctions.RHTower.PerronMiddleDictionary
import GaloisForLFunctions.RHTower.PerronRectangleResidue

/-!
# The Perron contour assembly

On a zero-free rectangle `[σ₀,a]×[−2πW,2πW]` the smoothed Chebyshev
sum splits into its main term and explicit contour errors:

`∑ Λ(n)(log(x/n))⁺ = x + (left tail + right tail)
   + (2π)⁻¹·(i·(bottom − top) + left edge)`.

The explicit formula gives the full `a`-line integral, the line splits
at `±W`, the middle matches the rectangle's right edge under `y = 2πw`,
and the rectangle winds once around `s = 1` with residue `x`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- **The Perron contour assembly**: the smoothed Chebyshev sum is
`x` plus tails and edge integrals of the zero-free rectangle. -/
theorem smoothed_chebyshev_contour_assembly {x a σ₀ W : ℝ}
    (hx : 0 < x) (ha1 : 1 < a) (ha2 : a ≤ 2) (hσ₀ : 0 < σ₀)
    (hσ₁ : σ₀ < 1) (hW : 0 < W)
    (hzf : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ a →
      |s.im| ≤ 2 * Real.pi * W → s ≠ 1 → riemannZeta s ≠ 0) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
        * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)
      = (x : ℂ)
      + ((∫ w in Set.Iic (-W),
            - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)))
        + ∫ w in Set.Ioi W,
            - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
            * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
              / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)))
      + (2 * Real.pi)⁻¹ •
          (Complex.I *
            ((∫ t in σ₀..a,
              - deriv riemannZeta ((t : ℂ)
                  + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((t : ℂ)
                  + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
              * ((x : ℂ) ^ ((t : ℂ)
                  + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
                / ((t : ℂ)
                  + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)))
            - ∫ t in σ₀..a,
              - deriv riemannZeta ((t : ℂ)
                  + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((t : ℂ)
                  + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
              * ((x : ℂ) ^ ((t : ℂ)
                  + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
                / ((t : ℂ)
                  + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)))
          + ∫ y in (-(2 * Real.pi * W))..(2 * Real.pi * W),
              - deriv riemannZeta ((σ₀ : ℂ) + y * Complex.I)
                / riemannZeta ((σ₀ : ℂ) + y * Complex.I)
              * ((x : ℂ) ^ ((σ₀ : ℂ) + y * Complex.I)
                / ((σ₀ : ℂ) + y * Complex.I) ^ (2 : ℕ))) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT0 : (0 : ℝ) < 2 * Real.pi * W := by positivity
  -- corner coordinates
  have hz1re : ((σ₀ : ℂ)
      + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I).re = σ₀ := by
    simp
  have hz1im : ((σ₀ : ℂ)
      + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I).im
      = -(2 * Real.pi * W) := by
    simp
  have hz2re : ((a : ℂ)
      + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I).re = a := by
    simp
  have hz2im : ((a : ℂ)
      + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I).im
      = 2 * Real.pi * W := by
    simp
  -- the rectangle residue
  have hrect := rectIntegral_perron_eq hx
    (z₁ := (σ₀ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
    (z₂ := (a : ℂ) + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
    (by rw [hz1re]; exact hσ₀)
    (by rw [hz1re]; exact hσ₁)
    (by rw [hz2re]; exact ha1)
    (by rw [hz1im]; linarith)
    (by rw [hz2im]; exact hT0)
    (by
      intro s hs1 hs2 hs3
      rw [hz1re, hz2re,
        uIcc_of_le (by linarith : σ₀ ≤ a)] at hs1
      rw [hz1im, hz2im,
        uIcc_of_le (by linarith :
          -(2 * Real.pi * W) ≤ 2 * Real.pi * W)] at hs2
      exact hzf s hs1.1 hs1.2 (abs_le.2 ⟨hs2.1, hs2.2⟩) hs3)
  unfold rectIntegral at hrect
  simp only [hz1re, hz1im, hz2re, hz2im, smul_eq_mul] at hrect
  set Bv : ℂ := ∫ t in σ₀..a,
    - deriv riemannZeta ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
      / riemannZeta ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
    * ((x : ℂ) ^ ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
      / ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) with hBv
  set Tv : ℂ := ∫ t in σ₀..a,
    - deriv riemannZeta ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
      / riemannZeta ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
    * ((x : ℂ) ^ ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
      / ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) with hTv
  set Rv : ℂ := ∫ y in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    - deriv riemannZeta ((a : ℂ) + y * Complex.I)
      / riemannZeta ((a : ℂ) + y * Complex.I)
    * ((x : ℂ) ^ ((a : ℂ) + y * Complex.I)
      / ((a : ℂ) + y * Complex.I) ^ (2 : ℕ)) with hRv
  set Lv : ℂ := ∫ y in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    - deriv riemannZeta ((σ₀ : ℂ) + y * Complex.I)
      / riemannZeta ((σ₀ : ℂ) + y * Complex.I)
    * ((x : ℂ) ^ ((σ₀ : ℂ) + y * Complex.I)
      / ((σ₀ : ℂ) + y * Complex.I) ^ (2 : ℕ)) with hLv
  have hI := Complex.I_sq
  have hRight : Rv = 2 * (Real.pi : ℂ) * (x : ℂ)
      + (Complex.I * (Bv - Tv) + Lv) := by
    linear_combination (-Complex.I) * hrect
      + (Rv - Lv - 2 * (Real.pi : ℂ) * (x : ℂ)) * hI
  rw [smoothed_chebyshev_eq_perron_integral hx ha1,
    integral_split_three
      (integrable_perron_zeta_integrand hx ha1 ha2) hW.le,
    integral_middle_eq_interval hW.le, ← hRv, hRight, smul_add]
  have hxterm : (2 * Real.pi)⁻¹
      • (2 * (Real.pi : ℂ) * (x : ℂ)) = (x : ℂ) := by
    rw [Complex.real_smul]
    push_cast
    have hπne : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ne_of_gt hπ0)
    field_simp
  rw [hxterm]
  abel

end RHTower
