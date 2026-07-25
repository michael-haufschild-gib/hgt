import GaloisForLFunctions.RHTower.SmoothAFEZetaContour
import GaloisForLFunctions.RHTower.SmoothAFEZetaLeftLineBound

/-!
# Infinite-contour assembly for the Gaussian smooth zeta AFE

Both vertical edges of the critical-line rectangle are now unconditionally
Bochner-integrable.  This module passes their symmetric truncations to full-line
integrals and isolates the only remaining contour-limit obligation: decay of the
two horizontal zeta-weighted Gaussian integrals.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology

theorem smoothAFEZetaMellinIntegrand_right_one_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Complex.VerticalIntegrable
      (smoothAFEZetaMellinIntegrand (linePt τ) x) 1 := by
  apply smoothAFEZetaMellinIntegrand_verticalIntegrable hx (by norm_num)
  rw [linePt_re]
  norm_num

theorem tendsto_smoothAFEZetaMellinIntegrand_left_one_intervalIntegral
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            (((-1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaMellinIntegrand (linePt τ) x
          (((-1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaMellinIntegrand_left_one_verticalIntegrable hx τ)
    tendsto_neg_atTop_atBot tendsto_id

theorem tendsto_smoothAFEZetaMellinIntegrand_right_one_intervalIntegral
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        smoothAFEZetaMellinIntegrand (linePt τ) x
          (((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (smoothAFEZetaMellinIntegrand_right_one_verticalIntegrable hx τ)
    tendsto_neg_atTop_atBot tendsto_id

/-- Once the horizontal Gaussian edges vanish, the finite two-pole rectangle
identity passes to the exact infinite vertical-line contour shift.  All other
inputs of this theorem are discharged unconditionally in the corpus. -/
theorem smoothAFEZetaMellin_infinite_contour_shift_line_of_horizontal_tendsto
    {x τ : ℝ} (hx : 0 < x)
    (hbottom : Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1)..1,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0))
    (htop : Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1)..1,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0)) :
    I • (∫ v : ℝ,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta (linePt τ) +
          smoothAFEZetaShiftedPoleResidue (linePt τ) x) := by
  let F : ℂ → ℂ := smoothAFEZetaMellinIntegrand (linePt τ) x
  have hright := tendsto_smoothAFEZetaMellinIntegrand_right_one_intervalIntegral hx τ
  have hleft := tendsto_smoothAFEZetaMellinIntegrand_left_one_intervalIntegral hx τ
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝
        (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I *
          (riemannZeta (linePt τ) +
            smoothAFEZetaShiftedPoleResidue (linePt τ) x) := by
    filter_upwards [eventually_gt_atTop |τ|] with T hT
    simpa [F] using
      smoothAFEZetaMellin_finite_contour_shift_line hx hT
  have hrhs : Tendsto
      (fun _T : ℝ =>
        2 * Real.pi * I *
          (riemannZeta (linePt τ) +
            smoothAFEZetaShiftedPoleResidue (linePt τ) x))
      atTop
      (𝓝 (2 * Real.pi * I *
        (riemannZeta (linePt τ) +
          smoothAFEZetaShiftedPoleResidue (linePt τ) x))) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

end RHTower
