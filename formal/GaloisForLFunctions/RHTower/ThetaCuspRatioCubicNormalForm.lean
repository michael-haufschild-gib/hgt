import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicCoordinateDivision
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def nonlinearTransverseCore : Poly := coordinateQuotient Coord.J (nonlinearShift scaledSlope)
def nonlinearCubicCore : Poly := coordinateQuotient Coord.U
  (coordinateQuotient Coord.U (coordinateQuotient Coord.U (nonlinearShift scaledSlope)))

theorem nonlinearCubicCore_line (r : ℂ) :
    affineLine r nonlinearCubicCore=nonlinearSlopeCore r := by
  simp only [nonlinearCubicCore,affineLine_quotient,nonlinearSlopeCore]

theorem nonlinearCubicCore_zero (r : ℂ) :
    eval (basePoint 0 r 0) nonlinearCubicCore=1944*axisMinorMass-63*principalMass*r^2 := by
  rw [←affineLine_eval,nonlinearCubicCore_line,nonlinearSlopeCore_zero]

theorem nonlinearSlope_normal_form (h r s : ℂ) :
    eval (basePoint h r s) (nonlinearShift scaledSlope)=
      s*eval (basePoint h r s) nonlinearTransverseCore+
      h^3*eval (basePoint h r 0) nonlinearCubicCore := by
  have he := congrArg (eval (basePoint h r s)) (coordinate_division Coord.J (nonlinearShift scaledSlope))
  simp only [map_add,map_mul,eval_X,basePoint,coordinateReset_eval] at he
  have hb : (fun j => if j=Coord.J then (0:ℂ) else basePoint h r s j)=basePoint h r 0 := by
    funext j
    cases j <;> rfl
  simp only [basePoint] at hb
  rw [hb] at he
  have hc := congrArg (Polynomial.eval h) (nonlinearSlope_factor r)
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,affineLine_eval,
    ←nonlinearCubicCore_line] at hc
  simpa only [nonlinearTransverseCore,hc] using he

theorem nonlinearShift_zero (r s : ℂ) :
    eval (basePoint 0 r s) (nonlinearShift scaledSlope)=7776*principalMass*s := by
  rw [nonlinearShift_eval,scaledSlope_zero]
  ring

theorem nonlinearTransverseCore_zero (r s : ℂ) :
    eval (basePoint 0 r s) nonlinearTransverseCore=7776*principalMass := by
  have hp : coordinateReset Coord.U (nonlinearShift scaledSlope)=C (7776*principalMass)*X Coord.J := by
    apply MvPolynomial.funext
    intro v
    rw [coordinateReset_eval]
    have hb : (fun j => if j=Coord.U then (0:ℂ) else v j)=basePoint 0 (v .K) (v .J) := by
      funext j
      cases j <;> rfl
    rw [hb,nonlinearShift_zero]
    simp
  have hz : coordinateReset Coord.U (coordinateReset Coord.J (nonlinearShift scaledSlope))=0 := by
    apply MvPolynomial.funext
    intro v
    rw [coordinateReset_eval,coordinateReset_eval]
    have hb : (fun j => if j=Coord.J then (0:ℂ) else if j=Coord.U then 0 else v j)=
        basePoint 0 (v .K) 0 := by
      funext j
      cases j <;> rfl
    rw [hb,nonlinearShift_zero]
    simp
  have he := congrArg (coordinateReset Coord.U) (coordinate_division Coord.J (nonlinearShift scaledSlope))
  simp only [map_add,map_mul,coordinateReset_X,show Coord.J≠Coord.U by decide,if_false,hp,hz,add_zero] at he
  have hq : coordinateReset Coord.U nonlinearTransverseCore=C (7776*principalMass) := by
    apply mul_left_cancel₀ (MvPolynomial.X_ne_zero Coord.J)
    simpa only [nonlinearTransverseCore,map_mul,mul_comm] using he.symm
  have hv := congrArg (eval (basePoint 0 r s)) hq
  rw [coordinateReset_eval] at hv
  have hb : (fun j => if j=Coord.U then (0:ℂ) else basePoint 0 r s j)=basePoint 0 r s := by
    funext j
    cases j <;> rfl
  simpa only [hb,eval_C] using hv

def cubicSheet (h r : ℝ) : ℝ := r*(1/12-7*h/72)+(r^2/144)*h^2-(7*r^2/432)*h^3

theorem nonlinear_barrier_above_cubic {h r t : ℝ} (hr : 0≤r) (hh : h≤4/5)
    (he : r*(1/12-7*h/72)<t-h^2*t^2) : cubicSheet h r<t := by
  let a : ℝ := r*(1/12-7*h/72)
  have ha : 0≤a := by dsimp [a]; exact mul_nonneg hr (by linarith)
  have hat : a<t := lt_of_lt_of_le he (sub_le_self _ (mul_nonneg (sq_nonneg h) (sq_nonneg t)))
  have hs : a^2≤t^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg h)
  have hB : cubicSheet h r+49*r^2*h^4/5184=a+h^2*a^2 := by dsimp [cubicSheet,a]; ring
  have hc : 0≤49*r^2*h^4/5184 := by positivity
  change a<t-h^2*t^2 at he
  calc
    cubicSheet h r ≤ cubicSheet h r+49*r^2*h^4/5184 := le_add_of_nonneg_right hc
    _ = a+h^2*a^2 := hB
    _ ≤ a+h^2*t^2 := by linarith only [hm]
    _ < t := by linarith only [he]

end
end HTGeometry.ThetaRatioInfinity
