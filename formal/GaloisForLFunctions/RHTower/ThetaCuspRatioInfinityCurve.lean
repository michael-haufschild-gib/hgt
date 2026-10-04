import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityFlow
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare


def vectorAt (h r t : ℂ) (i : Coord) : ℂ :=
  eval (basePoint h r t) (infinityField i)

def baseCurve (h r t z : ℂ) (i : Coord) : ℂ :=
  basePoint h r t i+z*vectorAt h r t i

def sourceCurve (h r t z : ℂ) : Coord → ℂ :=
  sourcePoint (baseCurve h r t z .U) (baseCurve h r t z .K) (baseCurve h r t z .J)

@[simp] theorem baseCurve_zero (h r t : ℂ) : baseCurve h r t 0=basePoint h r t := by
  funext i
  simp [baseCurve]

@[simp] theorem sourceCurve_zero (h r t : ℂ) : sourceCurve h r t 0=sourcePoint h r t := by
  simp [sourceCurve,basePoint]

theorem baseCurve_derivative (h r t : ℂ) : HasDerivAt (baseCurve h r t) (vectorAt h r t) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa [baseCurve] using ((hasDerivAt_id (0:ℂ)).mul_const (vectorAt h r t i)).const_add
    (basePoint h r t i)

theorem sourceCurve_derivative (h r t : ℂ) (hh : h≠0) :
    HasDerivAt (sourceCurve h r t)
      (fun i => h*eval (sourcePoint h r t) (squareField i)) 0 := by
  have dh := hasDerivAt_pi.mp (baseCurve_derivative h r t) Coord.U
  have dr := hasDerivAt_pi.mp (baseCurve_derivative h r t) Coord.K
  have dt := hasDerivAt_pi.mp (baseCurve_derivative h r t) Coord.J
  have hc := field_change h r t hh
  apply hasDerivAt_pi.mpr
  intro i
  cases i with
  | U =>
      convert! (hasDerivAt_const (0:ℂ) (9:ℂ)).sub (dr.mul (dh.pow 2)) using 1 <;>
        simp [sourceCurve,sourcePoint,baseCurve,basePoint]
      all_goals
        rw [← hc.1]
        simp only [vectorAt]
        ring
  | K =>
      have hn : baseCurve h r t 0 Coord.U≠0 := by simpa [basePoint] using hh
      convert! dh.inv hn using 1 <;> simp [sourceCurve,sourcePoint,baseCurve,basePoint]
      all_goals
        rw [← hc.2.1]
        simp only [vectorAt]
        field_simp [hh]
  | J =>
      convert! ((hasDerivAt_const (0:ℂ) (1:ℂ)).sub (dt.mul dh)).div_const 3 using 1 <;>
        simp [sourceCurve,sourcePoint,baseCurve,basePoint]
      all_goals
        rw [← hc.2.2]
        simp only [vectorAt]
        ring

theorem baseEval_derivative (P : Poly) (h r t : ℂ) :
    HasDerivAt (fun z => eval (baseCurve h r t z) P)
      (eval (basePoint h r t) (flow infinityField P)) 0 := by
  have hd := GaloisForLFunctions.HTGeometry.hasDerivAt_mvPolynomial_eval_comp P
    (baseCurve_derivative h r t)
  simpa only [baseCurve_zero,flow,map_sum,map_mul,vectorAt] using hd

theorem sourceEval_derivative (P : Poly) (h r t : ℂ) (hh : h≠0) :
    HasDerivAt (fun z => eval (sourceCurve h r t z) P)
      (h*eval (sourcePoint h r t) (squareLie P)) 0 := by
  have hd := GaloisForLFunctions.HTGeometry.hasDerivAt_mvPolynomial_eval_comp P
    (sourceCurve_derivative h r t hh)
  convert hd using 1
  simp only [sourceCurve_zero,squareLie,flow,map_sum,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end HTGeometry.ThetaRatioInfinity
