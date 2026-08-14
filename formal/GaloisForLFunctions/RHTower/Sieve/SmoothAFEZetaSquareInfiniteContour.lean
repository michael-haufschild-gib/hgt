import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareContour
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareVerticalIntegrability
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareHorizontalDecay

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace RHTower.Sieve

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

theorem smoothAFEZetaSquareMellin_infinite_contour_shift_line
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    I • (∫ v : ℝ,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ 2 +
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
          (riemannZeta (linePt tau) ^ 2 +
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
          (riemannZeta (linePt tau) ^ 2 +
            confluentResidueCoeff
              (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
              (1 - linePt tau)))
      atTop
      (𝓝 (2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ 2 +
          confluentResidueCoeff
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)))) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

end RHTower.Sieve
