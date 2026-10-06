import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockPrincipalJets
import Mathlib.Analysis.Convex.Deriv
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def compactMinorClockZeroModel : Poly :=
  142586608414333163390281023750144*(1+X Coord.J)*(1-3*X Coord.J)

theorem compactMinor_clock_zero (r z : ℂ) :
    eval (basePoint 0 r z) compactMinor=eval (basePoint 0 r z) compactMinorClockZeroModel := by
  rw [(compactMinorZeroNorm r z).property]
  norm_num [compactMinorZeroNorm,compactMinorClockZeroModel,basePoint,Nat.rawCast,Int.rawCast]
  ring

theorem compactSlope_clock_zero (r z : ℂ) :
    eval (basePoint 0 r z) compactSlope=
      9*6844157203887991842733489140006912*(1-9*z^2) := by
  rw [compactSlope_zero_lie,defectLie_clock_zero_congr _ _ compactMinor_clock_zero]
  unfold defectLie
  rw [flow_expand]
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  norm_num [compactMinorClockZeroModel,defectField,basePoint,pderiv_X,Pi.single_apply,hUJ,hKJ]
  ring

def kineticClockPrincipal (z : ℝ) : ℝ :=
  6844157203887991842733489140006912*(1-9*z^2)

theorem compactSlope_clock_zero_real (r z : ℝ) :
    (eval (basePoint 0 (r:ℂ) (z:ℂ)) compactSlope).re=9*kineticClockPrincipal z := by
  rw [compactSlope_clock_zero]
  norm_num [kineticClockPrincipal,←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem kineticClockPrincipal_factor (z : ℝ) :
    kineticClockPrincipal z=6844157203887991842733489140006912*(1-3*z)*(1+3*z) := by
  unfold kineticClockPrincipal
  ring

theorem kineticClockPrincipal_pos (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1/3) :
    0 < kineticClockPrincipal z := by
  rw [kineticClockPrincipal_factor]
  apply mul_pos
  · apply mul_pos (by norm_num)
    linarith
  · linarith

theorem kineticClockPrincipal_boundary : kineticClockPrincipal (1/3)=0 := by
  norm_num [kineticClockPrincipal]

theorem kineticClockPrincipal_hasDerivAt (z : ℝ) :
    HasDerivAt kineticClockPrincipal
      (-18*6844157203887991842733489140006912*z) z := by
  have hd := ((((hasDerivAt_id z).pow 2).const_mul 9).const_sub 1).const_mul
    (6844157203887991842733489140006912:ℝ)
  apply hd.congr_deriv
  norm_num
  ring

theorem kineticClockPrincipal_second_derivative (z : ℝ) :
    deriv (deriv kineticClockPrincipal) z= -18*6844157203887991842733489140006912 := by
  have hd : deriv kineticClockPrincipal=fun z => -18*6844157203887991842733489140006912*z := by
    funext z
    exact (kineticClockPrincipal_hasDerivAt z).deriv
  rw [hd]
  simpa only [id_eq,mul_one] using
    ((hasDerivAt_id z).const_mul (-18*6844157203887991842733489140006912)).deriv

theorem kineticClockPrincipal_curvature_neg (z : ℝ) :
    deriv (deriv kineticClockPrincipal) z < 0 := by
  rw [kineticClockPrincipal_second_derivative]
  norm_num

theorem kineticClockPrincipal_cubic_gap (z : ℝ) :
    kineticClockPrincipal z-
        6844157203887991842733489140006912*(1-3*z)^2*(1+6*z)=
      18*6844157203887991842733489140006912*z^2*(1-3*z) := by
  unfold kineticClockPrincipal
  ring

theorem kineticClockPrincipal_cubic_lt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/3) :
    6844157203887991842733489140006912*(1-3*z)^2*(1+6*z) < kineticClockPrincipal z := by
  have he := kineticClockPrincipal_cubic_gap z
  have hp : 0 < 18*6844157203887991842733489140006912*z^2*(1-3*z) := by
    apply mul_pos
    · positivity
    · linarith
  linarith only [he,hp]

end
end HTGeometry.ThetaRatioKineticContraction
