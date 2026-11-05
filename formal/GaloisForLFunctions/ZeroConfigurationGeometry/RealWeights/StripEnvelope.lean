import GaloisForLFunctions.HTGeometry.IntervalPoincare
import Mathlib.Analysis.Complex.Basic


/-!
# Vertical energy envelopes

The fundamental theorem of calculus and Cauchy–Schwarz bound displacement
from the centre of a vertical unit segment by derivative energy. Young's
inequality leaves the central squared norm with coefficient `1 + ε`.
-/

open MeasureTheory Complex Set Filter
open scoped Topology

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry

private theorem norm_increment_sq_le {F G : ℝ → ℂ} {a b : ℝ}
    (hderiv : ∀ y, HasDerivAt F (G y) y) (hG : Continuous G) (hab : a ≤ b) :
    ‖F b - F a‖ ^ 2 ≤ (b - a) * ∫ y in a..b, ‖G y‖ ^ 2 := by
  have hftc : (∫ y in a..b, G y) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hG.intervalIntegrable a b)
  have hn := intervalIntegral.norm_integral_le_integral_norm (f := G) (μ := volume) hab
  have hcs : (∫ y in a..b, ‖G y‖) ^ 2 ≤ (b - a) * ∫ y in a..b, ‖G y‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact HTGeometry.sq_integral_le_length_mul hab (hG.norm.intervalIntegrable a b).1
      ((hG.norm.pow 2).intervalIntegrable a b).1
  rw [hftc] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs

/-- The derivative energy on a unit vertical segment controls displacement from its centre. -/
theorem norm_sub_sq_le_vertical_energy {F G : ℝ → ℂ}
    (hderiv : ∀ y, HasDerivAt F (G y) y) (hG : Continuous G)
    {v : ℝ} (hv : |v| ≤ 1 / 2) :
    ‖F v - F 0‖ ^ 2 ≤ ∫ y in (-1 / 2 : ℝ)..(1 / 2), ‖G y‖ ^ 2 := by
  have hv' := abs_le.mp hv
  have hnn : 0 ≤ ∫ y in (-1 / 2 : ℝ)..(1 / 2), ‖G y‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun y _ => sq_nonneg _)
  have hcont := hG.norm.pow 2
  by_cases hv0 : 0 ≤ v
  · have hh := norm_increment_sq_le hderiv hG hv0
    have hmono : (∫ y in (0 : ℝ)..v, ‖G y‖ ^ 2) ≤
        ∫ y in (-1 / 2 : ℝ)..(1 / 2), ‖G y‖ ^ 2 :=
      intervalIntegral.integral_mono_interval (by norm_num) hv0 hv'.2
        (Eventually.of_forall fun y => sq_nonneg _) (hcont.intervalIntegrable _ _)
    have hlen : v - 0 ≤ 1 := by linarith only [hv'.2]
    exact hh.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hv0)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlen hnn))
  · have hvn : v ≤ 0 := le_of_not_ge hv0
    have hh := norm_increment_sq_le hderiv hG hvn
    rw [norm_sub_rev] at hh
    have hmono : (∫ y in v..(0 : ℝ), ‖G y‖ ^ 2) ≤
        ∫ y in (-1 / 2 : ℝ)..(1 / 2), ‖G y‖ ^ 2 :=
      intervalIntegral.integral_mono_interval (by linarith only [hv'.1]) hvn (by norm_num)
        (Eventually.of_forall fun y => sq_nonneg _) (hcont.intervalIntegrable _ _)
    have hlen : 0 - v ≤ 1 := by linarith only [hv'.1]
    exact hh.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hvn)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlen hnn))

/-- A tunable strip envelope keeps the central transform with coefficient arbitrarily close
to one, charging only the vertical derivative energy for the remaining displacement. -/
theorem norm_sq_le_vertical_energy_envelope {F G : ℝ → ℂ} {ε v : ℝ}
    (hε : 0 < ε) (hderiv : ∀ y, HasDerivAt F (G y) y) (hG : Continuous G)
    (hv : |v| ≤ 1 / 2) :
    ‖F v‖ ^ 2 ≤ (1 + ε) * ‖F 0‖ ^ 2 +
      (1 + 1 / ε) * ∫ y in (-1 / 2 : ℝ)..(1 / 2), ‖G y‖ ^ 2 := by
  have htri : ‖F v‖ ≤ ‖F 0‖ + ‖F v - F 0‖ := by
    calc ‖F v‖ = ‖F 0 + (F v - F 0)‖ := by congr 1; ring
      _ ≤ ‖F 0‖ + ‖F v - F 0‖ := norm_add_le _ _
  have hy : (‖F 0‖ + ‖F v - F 0‖) ^ 2 ≤
      (1 + ε) * ‖F 0‖ ^ 2 + (1 + 1 / ε) * ‖F v - F 0‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    have he : ε * ((1 + ε) * ‖F 0‖ ^ 2 + (1 + 1 / ε) * ‖F v - F 0‖ ^ 2) -
        ε * (‖F 0‖ + ‖F v - F 0‖) ^ 2 = (ε * ‖F 0‖ - ‖F v - F 0‖) ^ 2 := by
      field_simp [hε.ne']
      ring
    exact sub_nonneg.mp (he.symm ▸ sq_nonneg (ε * ‖F 0‖ - ‖F v - F 0‖))
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans (hy.trans
    (by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_sub_sq_le_vertical_energy hderiv hG hv) (by positivity : 0 ≤ 1 + 1 / ε))))

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_sub_sq_le_vertical_energy
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_sq_le_vertical_energy_envelope
