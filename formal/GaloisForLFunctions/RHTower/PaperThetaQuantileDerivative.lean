import GaloisForLFunctions.RHTower.PaperThetaQuantileVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The actual integrable derivative of the closed theta quantile mode

Native bounded variation pays derivative integrability through real and
imaginary projections. Interior differentiation and the matching endpoint
traces then pay the exact primitive representation across the seam.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

theorem differentiableAt_closedQuantileMode (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (closedQuantileMode z) t.val := by
  apply (differentiableAt_pullback z t).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with x hx
  exact closedQuantileMode_interior z ⟨x, hx⟩

/-- Integrability is paid for the derivative of the literal complex mode, including the seam. -/
theorem intervalIntegrable_deriv_closedQuantileMode
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    IntervalIntegrable (deriv (closedQuantileMode z.val)) volume 0 1 := by
  have hb : BoundedVariationOn (closedQuantileMode z.val) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      (boundedVariationOn_closedQuantileMode_iff z.val).mpr z.property
  have hr := (Complex.reCLM.lipschitz.comp_boundedVariationOn hb).intervalIntegrable_deriv
  have hi := (Complex.imCLM.lipschitz.comp_boundedVariationOn hb).intervalIntegrable_deriv
  have hrc : IntervalIntegrable
      (fun t : ℝ => ((deriv (fun x => (closedQuantileMode z.val x).re) t : ℝ) : ℂ)) volume 0 1 :=
    ⟨Complex.ofRealCLM.integrable_comp hr.1, Complex.ofRealCLM.integrable_comp hr.2⟩
  have hic : IntervalIntegrable
      (fun t : ℝ => ((deriv (fun x => (closedQuantileMode z.val x).im) t : ℝ) : ℂ)) volume 0 1 :=
    ⟨Complex.ofRealCLM.integrable_comp hi.1, Complex.ofRealCLM.integrable_comp hi.2⟩
  apply (hrc.add (hic.mul_const Complex.I)).congr_uIoo
  intro t ht
  rw [uIoo_of_lt (show (0 : ℝ) < 1 by norm_num)] at ht
  have hd := (differentiableAt_closedQuantileMode z.val ⟨t, ht⟩).hasDerivAt
  have hr' : deriv (fun x => (closedQuantileMode z.val x).re) t =
      (deriv (closedQuantileMode z.val) t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd).deriv
  have hi' : deriv (fun x => (closedQuantileMode z.val x).im) t =
      (deriv (closedQuantileMode z.val) t).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd).deriv
  change ((deriv (fun x => (closedQuantileMode z.val x).re) t : ℝ) : ℂ) +
    ((deriv (fun x => (closedQuantileMode z.val x).im) t : ℝ) : ℂ)*Complex.I = _
  rw [hr', hi', Complex.re_add_im]

/-- The native mode is the primitive of its actual derivative up to the common trace. -/
theorem closedQuantileMode_eq_integral_deriv
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (t : Icc (0 : ℝ) 1) :
    closedQuantileMode z.val t.val =
      (∫ x in (0 : ℝ)..t.val, deriv (closedQuantileMode z.val) x) - 1 := by
  have hs : Icc (0 : ℝ) t.val ⊆ Icc 0 1 := Icc_subset_Icc le_rfl t.property.2
  have ht : IntervalIntegrable (deriv (closedQuantileMode z.val)) volume 0 t.val :=
    (intervalIntegrable_deriv_closedQuantileMode z).mono_set (by
      simpa only [uIcc_of_le t.property.1, uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    ((continuousOn_closedQuantileMode z).mono hs)
    (fun x hx => (differentiableAt_closedQuantileMode z.val
      ⟨x, ⟨hx.1, hx.2.trans_le t.property.2⟩⟩).hasDerivAt) ht
  rw [(closedQuantileMode_endpoints z.val).1] at hftc
  rw [hftc]
  ring

/-- The closed derivative current has exactly zero total mass. -/
theorem integral_deriv_closedQuantileMode
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    (∫ x in (0 : ℝ)..1, deriv (closedQuantileMode z.val) x) = 0 := by
  have h := closedQuantileMode_eq_integral_deriv z ⟨1, by norm_num⟩
  rw [(closedQuantileMode_endpoints z.val).2] at h
  linear_combination -h

end RHTower.PaperThetaEndpoint
