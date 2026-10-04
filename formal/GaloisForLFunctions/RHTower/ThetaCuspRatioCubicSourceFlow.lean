import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticSlopeBoundary
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73n (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
private theorem univ73n : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

def nonlinearB : Poly := X Coord.K*affineB+
  C (1/144:ℂ)*(X Coord.K)^2*(X Coord.U)^2-
  C (7/432:ℂ)*(X Coord.K)^2*(X Coord.U)^3
def nonlinearCoord : Coord → Poly
  | .U => X .U
  | .K => X .K
  | .J => X .J+nonlinearB
def nonlinearShift : Poly →+* Poly := eval₂Hom C nonlinearCoord
@[simp] theorem nonlinearShift_C (c : ℂ) : nonlinearShift (C c)=C c := by simp [nonlinearShift]
@[simp] theorem nonlinearShift_X (i : Coord) : nonlinearShift (X i)=nonlinearCoord i := by simp [nonlinearShift]

theorem nonlinearShift_eval (P : Poly) (h r s : ℂ) :
    eval (basePoint h r s) (nonlinearShift P)=
      eval (basePoint h r (s+r*(1/12-7*h/72)+(r^2/144)*h^2-(7*r^2/432)*h^3)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,nonlinearShift_X,eval_X,hp]
    congr 1
    cases i <;> simp [nonlinearCoord,nonlinearB,affineB,basePoint] <;> ring

def nonlinearField : Coord → Poly
  | .U => nonlinearShift (infinityField .U)
  | .K => nonlinearShift (infinityField .K)
  | .J => nonlinearShift (infinityField .J)-
      pderiv Coord.U nonlinearB*nonlinearShift (infinityField .U)-
      pderiv Coord.K nonlinearB*nonlinearShift (infinityField .K)

theorem nonlinearField_coord (i : Coord) :
    flow nonlinearField (nonlinearCoord i)=nonlinearShift (infinityField i) := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have huk : Coord.U≠Coord.K := by intro h; cases h
  have hjk : Coord.J≠Coord.K := by intro h; cases h
  cases i <;> simp [flow,univ73n,nonlinearCoord,nonlinearField,nonlinearB,affineB,
    pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hku,hju,hkj,huj,huk,hjk] <;> ring

theorem nonlinearShift_flow (P : Poly) :
    flow nonlinearField (nonlinearShift P)=nonlinearShift (flow infinityField P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [flow_C]
  | add p q hp hq => simp only [map_add,flow_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,flow_mul,flow_X,map_add,nonlinearShift_X,hp,nonlinearField_coord]

def planeJet3 (r : ℂ) (P : Poly) : ℂ :=
  planeValue r (pderiv Coord.U (pderiv Coord.U (pderiv Coord.U P)))

end
end HTGeometry.ThetaRatioInfinity
