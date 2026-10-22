import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonBasis
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceWronskianContinuation

/-! The actual normalizable solution meets the fixed original horizon domain exactly at connection zeros. -/
open Complex Set
namespace RHTower.D4BMLaplaceRadial
noncomputable section

/-- The physical opposite-horizon coefficient of the normalizable solution is the full connection coefficient. -/
theorem normalizable_opposite_coefficient (w chi : ℂ) (hw : w.im ≠ 0) :
    horizonOppositeCoefficient w chi (normalizable w chi) (normalizableFirst w chi) =
      connection w chi / (2*w) := by
  have hW := wronskian_eq_continued w chi hw (show (1/2:ℝ) ∈ Ioo 0 1 by constructor <;> norm_num)
  change wronskian w chi (1/2) / (-w) = _
  rw [hW]
  ring

/-- This is an exact original radial boundary-domain criterion, not an assumed pole label. -/
theorem normalizable_original_horizon_domain_iff (w chi : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) :
    OriginalHorizonC2 w (normalizable w chi) ↔ connection w chi=0 := by
  rw [original_homogeneous_horizon_domain_iff w chi hw hwr
    (fun b hb => (normalizable_derivatives_continued hb).1)
    (fun b hb => (normalizable_derivatives_continued hb).2)
    (fun b hb => normalizable_equation_continued hb)]
  rw [normalizable_opposite_coefficient w chi hw]
  have hw0 : w ≠ 0 := by intro he; apply hw; rw [he,Complex.zero_im]
  exact div_eq_zero_iff.trans (or_iff_left (mul_ne_zero (by norm_num) hw0))

end
end RHTower.D4BMLaplaceRadial
