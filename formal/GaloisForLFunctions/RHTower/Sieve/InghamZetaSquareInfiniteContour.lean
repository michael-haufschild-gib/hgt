import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareVerticalIntegrability

/-!
# Exact infinite contour shift for Ingham's zeta-square Mellin integral

Absolute vertical integrability and unconditional horizontal decay pass finite confluent residue
identity to full vertical lines.
-/

noncomputable section

open Complex MeasureTheory Filter Topology

namespace RHTower.Sieve

theorem tendsto_inghamZetaSquareMellinIntegrand_left_threeQuarter_intervalIntegral
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        inghamZetaSquareMellinIntegrand (linePt tau) x
          (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (inghamZetaSquareMellinIntegrand_left_threeQuarter_verticalIntegrable hx tau)
    tendsto_neg_atTop_atBot tendsto_id

theorem tendsto_inghamZetaSquareMellinIntegrand_right_two_intervalIntegral
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in (-T)..T,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((2 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ,
        inghamZetaSquareMellinIntegrand (linePt tau) x
          (((2 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (inghamZetaSquareMellinIntegrand_right_two_verticalIntegrable hx tau)
    tendsto_neg_atTop_atBot tendsto_id

/-- Exact full-line contour shift, including shifted double-pole residue packet. -/
theorem inghamZetaSquareMellin_infinite_contour_shift_line
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    I • (∫ v : ℝ,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((2 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ (2 : ℕ) +
          confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)) := by
  let F : ℂ → ℂ := inghamZetaSquareMellinIntegrand (linePt tau) x
  have hright := tendsto_inghamZetaSquareMellinIntegrand_right_two_intervalIntegral hx tau
  have hleft := tendsto_inghamZetaSquareMellinIntegrand_left_threeQuarter_intervalIntegral hx tau
  have hbottom := tendsto_inghamZetaSquareMellinIntegrand_horizontal_bottom hx tau
  have htop := tendsto_inghamZetaSquareMellinIntegrand_horizontal_top hx tau
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-3 / 4)..2, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-3 / 4)..2, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, F (((2 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T,
            F (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝
        (I • (∫ v : ℝ, F (((2 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ, F (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [F] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-3 / 4)..2, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-3 / 4)..2, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F (((2 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T,
          F (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I *
          (riemannZeta (linePt tau) ^ (2 : ℕ) +
            confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
              (1 - linePt tau)) := by
    filter_upwards [eventually_gt_atTop |tau|] with T hT
    have hfinite :=
      rectIntegral_inghamZetaSquareMellinIntegrand tau (-3 / 4) T hx
        (by norm_num) (by norm_num) hT
    rw [rectIntegral] at hfinite
    simpa [F, smul_eq_mul, sub_eq_add_neg] using hfinite
  have hrhs : Tendsto
      (fun _T : ℝ =>
        2 * Real.pi * I *
          (riemannZeta (linePt tau) ^ (2 : ℕ) +
            confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
              (1 - linePt tau)))
      atTop
      (𝓝 (2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ (2 : ℕ) +
          confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)))) := tendsto_const_nhds
  exact tendsto_nhds_unique (hlimit'.congr' hevent) hrhs

end RHTower.Sieve
