import GaloisForLFunctions.RHTower.BurnolCoPoissonFractionalKernel
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The Mellin transform of the indicator co-Poisson vector

The reciprocal-indicator co-Poisson value is the difference of two dilates of the fractional-part
kernel, so its Mellin transform on the critical strip is the corresponding difference of dilated
zeta factors:

`integral_0^infinity P_G(t) t^(-w) dt = (b^(-w) - b^w) zeta(w) / w`.

This is the explicit bridge between the extended Sonine space and the zeta function: the co-Poisson
vector of the indicator seed has nonvanishing Mellin transform exactly where zeta does not vanish.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem ofReal_inv_cpow_eq_cpow_neg {b : ℝ} (hb : 0 < b) (w : ℂ) :
    (((b⁻¹ : ℝ)) : ℂ) ^ w = ((b : ℝ) : ℂ) ^ (-w) := by
  have hbne : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  have hprod : ((b : ℝ) : ℂ) ^ w * (((b⁻¹ : ℝ)) : ℂ) ^ w = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg hb.le (le_of_lt (inv_pos.mpr hb)),
      ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hb), Complex.ofReal_one,
      Complex.one_cpow]
  rw [Complex.cpow_neg]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)

/-- **The Mellin transform of the reciprocal-indicator co-Poisson value.**  On the critical strip
it is the difference of the two dilated zeta factors of the window. -/
theorem integral_Ioi_burnolCoPoisson_reciprocalIndicator_cpow {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t *
          (t : ℂ) ^ (-w)) =
      (((b : ℝ) : ℂ) ^ (-w) - ((b : ℝ) : ℂ) ^ w) * (riemannZeta w / w) := by
  have hbinv : (0 : ℝ) < b⁻¹ := inv_pos.mpr hb
  have hint1 := integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 hb
  have hint2 := integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 hbinv
  have hae : (fun t : ℝ =>
      burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t *
        (t : ℂ) ^ (-w)) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ => ((Int.fract (b * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) -
        ((Int.fract (b⁻¹ * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
    filter_upwards [burnolCoPoissonRightSum_reciprocalIndicator_ae_fract hb hb1,
      ae_restrict_mem measurableSet_Ioi] with t ht htpos
    have htp : (0 : ℝ) < t := mem_Ioi.mp htpos
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htp)
    have hpow : ((t : ℝ) : ℂ)⁻¹ * (t : ℂ) ^ (-w) = (t : ℂ) ^ (-(w + 1)) := by
      rw [show (-(w + 1) : ℂ) = -1 + -w by ring, Complex.cpow_add _ _ htne,
        show ((t : ℝ) : ℂ) ^ (-1 : ℂ) = ((t : ℝ) : ℂ)⁻¹ by
          rw [Complex.cpow_neg, Complex.cpow_one]]
    rw [ht]
    have harg1 : t * b = b * t := mul_comm t b
    have harg2 : t / b = b⁻¹ * t := by
      rw [div_eq_mul_inv, mul_comm]
    rw [harg1, harg2]
    push_cast
    rw [← hpow]
    ring
  rw [integral_congr_ae hae]
  rw [integral_sub hint1 hint2, integral_Ioi_zero_fract_dilate_cpow hw0 hw1 hb,
    integral_Ioi_zero_fract_dilate_cpow hw0 hw1 hbinv, ofReal_inv_cpow_eq_cpow_neg hb]
  ring

end RHTower
