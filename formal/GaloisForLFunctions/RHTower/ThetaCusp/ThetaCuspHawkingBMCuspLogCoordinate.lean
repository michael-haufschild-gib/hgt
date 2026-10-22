import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspNativeIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspHeightOperator
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Complex.RealDeriv

/-!
The native cusp density and differential operator are transported exactly into logarithmic height.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- The exact square-root density factor in logarithmic cusp height. -/
def cuspLogWeight (t : ℝ) : ℂ := Real.exp (-t/2)

private theorem cuspLogWeight_deriv (t : ℝ) :
    HasDerivAt cuspLogWeight (-cuspLogWeight t/2) t := by
  have he := (((hasDerivAt_id t).neg.div_const 2).exp).ofReal_comp
  simp only [Pi.neg_apply,id_eq] at he
  change HasDerivAt cuspLogWeight _ t at he
  convert he using 1
  simp only [cuspLogWeight,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

/-- The actual cusp profile in the flat logarithmic-height measure. -/
def CuspHeightTest.logProfile (h : CuspHeightTest) (t : ℝ) : ℂ :=
  cuspLogWeight t*h.field (Real.exp t)

private theorem CuspHeightTest.logProfile_hasDerivAt (h : CuspHeightTest) (t : ℝ) :
    HasDerivAt h.logProfile (cuspLogWeight t*
      (-h.field (Real.exp t)/2+(Real.exp t:ℂ)*deriv h.field (Real.exp t))) t := by
  have hd := ((h.smooth.differentiable (by simp)) (Real.exp t)).hasDerivAt.scomp t
    (Real.hasDerivAt_exp t)
  have hp := (cuspLogWeight_deriv t).mul hd
  change HasDerivAt h.logProfile _ t at hp
  convert hp using 1
  simp only [Complex.real_smul,Function.comp_apply]
  ring

private theorem CuspHeightTest.logProfile_deriv (h : CuspHeightTest) :
    deriv h.logProfile = fun t => cuspLogWeight t*
      (-h.field (Real.exp t)/2+(Real.exp t:ℂ)*deriv h.field (Real.exp t)) := by
  funext t
  exact (h.logProfile_hasDerivAt t).deriv

/-- Logarithmic conjugation of the actual cusp differential expression is
exactly the free second derivative with threshold `5/4`. -/
theorem CuspHeightTest.log_operator_identity (h : CuspHeightTest) (t : ℝ) :
    cuspLogWeight t*(h.field (Real.exp t)-(Real.exp t:ℂ)^(2 : ℕ)*
      deriv (deriv h.field) (Real.exp t)) =
      (5/4:ℂ)*h.logProfile t-deriv (deriv h.logProfile) t := by
  have hd := ((h.smooth.differentiable (by simp)) (Real.exp t)).hasDerivAt.scomp t
    (Real.hasDerivAt_exp t)
  have hsd := (contDiff_infty_iff_deriv.mp h.smooth).2
  have hdd := ((hsd.differentiable (by simp)) (Real.exp t)).hasDerivAt.scomp t
    (Real.hasDerivAt_exp t)
  have hy := (Real.hasDerivAt_exp t).ofReal_comp
  have hp := (cuspLogWeight_deriv t).mul ((hd.neg.div_const 2).add (hy.mul hdd))
  rw [h.logProfile_deriv]
  have he := hp.deriv
  change deriv (fun r => cuspLogWeight r*
    (-h.field (Real.exp r)/2+(Real.exp r:ℂ)*deriv h.field (Real.exp r))) t = _ at he
  rw [he]
  simp only [Complex.real_smul,CuspHeightTest.logProfile,Function.comp_apply,
    Pi.add_apply,Pi.mul_apply,Pi.neg_apply]
  ring

private theorem cuspLogWeight_sq (t : ℝ) : cuspLogWeight t^(2 : ℕ)*(Real.exp t:ℂ) = 1 := by
  have hr : Real.exp (-t/2)^(2 : ℕ)*Real.exp t = 1 := by
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    rw [show -t/2 + -t/2 + t = 0 by ring,Real.exp_zero]
  change (Real.exp (-t/2):ℂ)^(2 : ℕ)*(Real.exp t:ℂ) = 1
  exact_mod_cast hr

/-- Exact logarithmic-height transport of a native cusp pairing. -/
theorem integral_cusp_pairing_log (a b : ℝ → ℂ) :
    (∫ y in Ioi 2, conj (a y)*b y/(y:ℂ)^(2 : ℕ)) =
      ∫ t in Ioi (Real.log 2), conj (cuspLogWeight t*a (Real.exp t))*
        (cuspLogWeight t*b (Real.exp t)) := by
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (Real.log 2)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun y => conj (a y)*b y/(y:ℂ)^(2 : ℕ))
  rw [Real.image_exp_Ioi,Real.exp_log (by norm_num : (0:ℝ)<2)] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hy : (Real.exp t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  have hc : conj (cuspLogWeight t) = cuspLogWeight t := Complex.conj_ofReal _
  rw [abs_of_pos (Real.exp_pos t),Complex.real_smul,map_mul,hc]
  have hs := cuspLogWeight_sq t
  field_simp
  linear_combination -(conj (a (Real.exp t))*b (Real.exp t))*hs

/-- The original modular cusp embedding is isometric in logarithmic height;
this uses its actual native measure and its constructed operator-domain vector. -/
theorem CuspHeightTest.logProfile_inner (h k : CuspHeightTest) :
    inner ℂ (h.operatorVector : Space) (k.operatorVector : Space) =
      ∫ t in Ioi (Real.log 2), conj (h.logProfile t)*k.logProfile t := by
  rw [h.operatorVector_inner,integral_cusp_pairing_log]
  rfl

end
end RHTower.D4BMModularCore
