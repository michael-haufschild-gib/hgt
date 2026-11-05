import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Two-sided bounds for the common incomplete-gamma mass

A tangent bound for the reciprocal square root retains two further terms
of the gamma expansion, with an explicit signed cubic remainder.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ThetaCuspSections.FifthAtomTail

private theorem reciprocal_sqrt_tangent {q t : ℝ} (hq : 0<q) (ht : 0<t) :
 1/Real.sqrt q-(t-q)/(2*q*Real.sqrt q)≤t^(-1/2:ℝ) := by
 have hu := Real.sqrt_pos.mpr ht
 have hv := Real.sqrt_pos.mpr hq
 have hu2 := Real.sq_sqrt ht.le
 have hv2 := Real.sq_sqrt hq.le
 rw [show (-1/2:ℝ)= -(1/2) by norm_num,Real.rpow_neg,← Real.sqrt_eq_rpow]
 apply (le_inv_iff₀ hu).mpr
 have h : 0≤(Real.sqrt t-Real.sqrt q)^2*(Real.sqrt t+2*Real.sqrt q) :=
  mul_nonneg (sq_nonneg _) (by positivity)
 apply (mul_le_mul_iff_right₀ (show 0<2*q*Real.sqrt q by positivity)).mp
 field_simp [hq.ne',hv.ne']
 nlinarith only [h,hu2,hv2]

end GaloisForLFunctions.ThetaCuspSections.FifthAtomTail
