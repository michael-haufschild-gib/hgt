import GaloisForLFunctions.HTGeometry.BetaReflectionKernel
import GaloisForLFunctions.HTGeometry.HalfLineChart
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Mellin kernel of `1 / (1 + y)`

Substituting `x = y / (1 + y)` carries the Beta integral of complementary arguments on the unit
interval to the Mellin integral of `1 / (1 + y)` on the half line.  Combined with the reflection
value of that Beta integral this evaluates the kernel:

`∫_0^∞ y^{w-1} / (1 + y) dy = π / sin (π w)` on the strip `0 < Re w < 1`.

It is the kernel of the Mellin representation of `∑_{n ≥ 1} x / (n^s + x)`, whose contour shifts
produce the asymptotic expansion of a canonical product's Euler logarithmic derivative.
-/

open Set MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

/-- The substituted integrand matches the Beta weight, pointwise on the unit interval. -/
theorem halfLineChart_integrand {w : ℂ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |((1 - x) ^ 2)⁻¹| • (((halfLineChart x : ℝ) : ℂ) ^ (w - 1) / (1 + ((halfLineChart x : ℝ) : ℂ)))
      = (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hone : (0 : ℝ) < 1 - x := by linarith
  set u : ℂ := ((1 - x : ℝ) : ℂ) with hudef
  have hu : u ≠ 0 := by
    rw [hudef]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hone)
  have harg : u.arg ≠ Real.pi := by
    rw [hudef, Complex.arg_ofReal_of_nonneg (le_of_lt hone)]
    exact ne_of_lt Real.pi_pos
  have hucast : u = 1 - (x : ℂ) := by
    rw [hudef]
    push_cast
    ring
  -- the Mellin denominator
  have honeC : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    rw [← hucast]
    exact hu
  have hden : (1 : ℂ) + ((halfLineChart x : ℝ) : ℂ) = u⁻¹ := by
    rw [halfLineChart, hudef]
    push_cast
    field_simp
    ring
  -- the power splits over the positive factors
  have hsplit : ((halfLineChart x : ℝ) : ℂ) ^ (w - 1) = (x : ℂ) ^ (w - 1) * u ^ (1 - w) := by
    have hchart : halfLineChart x = x * (1 - x)⁻¹ := by
      rw [halfLineChart, div_eq_mul_inv]
    rw [hchart, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (le_of_lt hx0) (by positivity : (0 : ℝ) ≤ (1 - x)⁻¹)]
    congr 1
    rw [Complex.ofReal_inv, ← hudef, Complex.inv_cpow u _ harg, ← Complex.cpow_neg]
    congr 1
    ring
  have hjac : (((1 - x) ^ 2 : ℝ) : ℂ)⁻¹ = u ^ (-(2 : ℂ)) := by
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, hudef]
    push_cast
    ring
  have habs : |((1 - x) ^ 2)⁻¹| = ((1 - x) ^ 2)⁻¹ := abs_of_pos (by positivity)
  rw [hsplit, hden, habs, Complex.real_smul]
  have hcastinv : ((((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) = (((1 - x) ^ 2 : ℝ) : ℂ)⁻¹ := by
    push_cast
    ring
  rw [hcastinv, hjac]
  rw [div_eq_mul_inv, inv_inv]
  have hcombine : u ^ (1 - w) * u = u ^ (2 - w) := by
    rw [show (2 : ℂ) - w = (1 - w) + 1 by ring, Complex.cpow_add _ _ hu]
    simp
  calc u ^ (-(2 : ℂ)) * ((x : ℂ) ^ (w - 1) * u ^ (1 - w) * u)
      = (x : ℂ) ^ (w - 1) * (u ^ (-(2 : ℂ)) * (u ^ (1 - w) * u)) := by ring
    _ = (x : ℂ) ^ (w - 1) * (u ^ (-(2 : ℂ)) * u ^ (2 - w)) := by rw [hcombine]
    _ = (x : ℂ) ^ (w - 1) * u ^ (-w) := by
        rw [← Complex.cpow_add _ _ hu]
        congr 2
        ring
    _ = (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w) := by rw [hucast]

/-- **The Mellin kernel of `1 / (1 + y)`.**  On the critical strip the Mellin transform of the
Cauchy kernel is the reflection kernel. -/
theorem integral_halfLine_reflection {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1) :
    (∫ y in Ioi (0 : ℝ), ((y : ℂ) ^ (w - 1) / (1 + (y : ℂ))))
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w) := by
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := halfLineChart) (f' := fun x : ℝ => ((1 - x) ^ 2)⁻¹)
    (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun x hx => hasDerivWithinAt_halfLineChart hx) halfLineChart_injOn
    (fun y : ℝ => ((y : ℂ) ^ (w - 1) / (1 + (y : ℂ))))
  rw [halfLineChart_image] at hchange
  rw [hchange]
  have hcongr : (∫ x in Ioo (0 : ℝ) 1, |((1 - x) ^ 2)⁻¹| •
        (((halfLineChart x : ℝ) : ℂ) ^ (w - 1) / (1 + ((halfLineChart x : ℝ) : ℂ))))
      = ∫ x in Ioo (0 : ℝ) 1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    exact halfLineChart_integrand hx
  rw [hcongr]
  have hinterval : (∫ x in (0 : ℝ)..1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w)))
      = ∫ x in Ioo (0 : ℝ) 1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← hinterval]
  exact integral_unitInterval_reflection hw hw1

/-- **The Mellin transform of the Cauchy kernel `u / (1 + u)`.**  On the strip `-1 < Re s < 0` it is
the negative reflection kernel. -/
theorem mellin_cauchyKernel {s : ℂ} (hs : -1 < s.re) (hs0 : s.re < 0) :
    (∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ (s - 1) * ((u : ℂ) / (1 + (u : ℂ)))))
      = -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) := by
  have hshift : (∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ (s - 1) * ((u : ℂ) / (1 + (u : ℂ)))))
      = ∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ ((s + 1) - 1) / (1 + (u : ℂ))) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hupos : (0 : ℝ) < u := hu
    have hune : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hupos)
    have hpow : (u : ℂ) ^ (s - 1) * (u : ℂ) = (u : ℂ) ^ ((s + 1) - 1) := by
      rw [show (s + 1) - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ hune]
      simp
    calc (u : ℂ) ^ (s - 1) * ((u : ℂ) / (1 + (u : ℂ)))
        = ((u : ℂ) ^ (s - 1) * (u : ℂ)) / (1 + (u : ℂ)) := by ring
      _ = (u : ℂ) ^ ((s + 1) - 1) / (1 + (u : ℂ)) := by rw [hpow]
  rw [hshift]
  rw [integral_halfLine_reflection (w := s + 1) (by simp; linarith) (by simp; linarith)]
  have hsin : Complex.sin ((Real.pi : ℂ) * (s + 1)) = -Complex.sin ((Real.pi : ℂ) * s) := by
    rw [show (Real.pi : ℂ) * (s + 1) = (Real.pi : ℂ) * s + (Real.pi : ℂ) by ring,
      Complex.sin_add_pi]
  rw [hsin]
  ring

end GaloisForLFunctions.HTGeometry
