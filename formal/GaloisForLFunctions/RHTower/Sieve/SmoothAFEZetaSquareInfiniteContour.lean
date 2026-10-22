import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareContour
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareVerticalIntegrability
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareHorizontalDecay

/-!
# Infinite contour shift for the Gaussian smoothed zeta-square integrand

For `s = 1/2 + iτ` on the critical line and `x > 0`, the Gaussian Mellin integrand
`F(w) = ζ(s + w)^2 x^w e^(w^2) / w` has poles inside the strip `-1 < Re w < 1` only at `w = 0`
(residue `ζ(s)^2`) and at the double pole `w = 1 - s`. Passing from finite rectangles to the full
strip, using vertical integrability on `Re w = ±1` and the decay of the horizontal edges, gives the
infinite contour identity between the two vertical line integrals and the residues.

## Main results

- `tendsto_smoothAFEZetaSquareMellinIntegrand_left_one_intervalIntegral`: the truncated integral of
  `F(-1 + iv)` over `[-T, T]` converges to the full line integral as `T → ∞`.
- `tendsto_smoothAFEZetaSquareMellinIntegrand_right_one_intervalIntegral`: the same on `Re w = 1`.
- `smoothAFEZetaSquareMellin_infinite_contour_shift_line`:
  `i ∫ F(1 + iv) dv - i ∫ F(-1 + iv) dv = 2πi (ζ(s)^2 + Res_{w = 1 - s} F)`, where the residue is
  `confluentResidueCoeff` of the pole-filled numerator at `1 - s`.

## Hypotheses

Unconditional; the only assumption is `x > 0`.
-/

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace RHTower.Sieve

/-- For `x > 0`, the integrals of `ζ(s + w)^2 x^w e^(w^2)/w` over `w = -1 + iv`, `v ∈ [-T, T]`,
converge to the full line integral as `T → ∞` (`s = 1/2 + iτ`). -/
theorem tendsto_smoothAFEZetaSquareMellinIntegrand_left_one_intervalIntegral
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            (((-1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          (((-1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaSquareMellinIntegrand_left_one_verticalIntegrable hx tau)
    tendsto_neg_atTop_atBot tendsto_id

/-- For `x > 0`, the integrals of `ζ(s + w)^2 x^w e^(w^2)/w` over `w = 1 + iv`, `v ∈ [-T, T]`,
converge to the full line integral as `T → ∞` (`s = 1/2 + iτ`). -/
theorem tendsto_smoothAFEZetaSquareMellinIntegrand_right_one_intervalIntegral
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          (((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaSquareMellinIntegrand_right_one_verticalIntegrable hx tau)
    tendsto_neg_atTop_atBot tendsto_id

/-- Infinite contour shift for `x > 0` and `s = 1/2 + iτ`: the line integral on `Re w = 1` minus the
one on `Re w = -1` equals `2πi (ζ(s)^2 + residue at w = 1 - s)`; proved as the `T → ∞` limit of
the rectangle residue theorem. -/
theorem smoothAFEZetaSquareMellin_infinite_contour_shift_line
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    I • (∫ v : ℝ,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ (2 : ℕ) +
          confluentResidueCoeff
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)) := by
  let F : ℂ → ℂ :=
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
  have hright :=
    tendsto_smoothAFEZetaSquareMellinIntegrand_right_one_intervalIntegral hx tau
  have hleft :=
    tendsto_smoothAFEZetaSquareMellinIntegrand_left_one_intervalIntegral hx tau
  have hbottom :=
    tendsto_smoothAFEZetaSquareMellinIntegrand_horizontal_bottom hx tau
  have htop :=
    tendsto_smoothAFEZetaSquareMellinIntegrand_horizontal_top hx tau
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T,
            F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T,
            F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝
        (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ,
            F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T,
          F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T,
          F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I *
          (riemannZeta (linePt tau) ^ (2 : ℕ) +
            confluentResidueCoeff
              (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
              (1 - linePt tau)) := by
    filter_upwards [eventually_gt_atTop |tau|] with T hT
    have hfinite :=
      rectIntegral_smoothAFEZetaSquareMellinIntegrand tau T hx hT
    rw [rectIntegral] at hfinite
    simpa [F, smul_eq_mul, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto
      (fun _T : ℝ =>
        2 * Real.pi * I *
          (riemannZeta (linePt tau) ^ (2 : ℕ) +
            confluentResidueCoeff
              (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
              (1 - linePt tau)))
      atTop
      (𝓝 (2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ (2 : ℕ) +
          confluentResidueCoeff
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)))) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

end RHTower.Sieve
