import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicSourceFlow
import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicJetAlgebra
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73c (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

theorem nonlinearShift_partial (P : Poly) (i : Coord) :
    pderiv i (nonlinearShift P)=nonlinearShift (pderiv i P)+
      pderiv i nonlinearB*nonlinearShift (pderiv Coord.J P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]; ring
  | mul_X p j hp =>
    simp only [map_mul,pderiv_mul,map_add,nonlinearShift_X,hp]
    cases i <;> cases j <;>
      simp [nonlinearCoord,nonlinearB,affineB,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply] <;> ring

theorem nonlinearShift_first (P : Poly) (r : ℂ) :
    planeJet1 r (nonlinearShift P)=affineJet1 r P := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  simp [planeJet1,planeValue,nonlinearShift_partial,nonlinearShift_eval,nonlinearB,affineB,
    affineJet1,criticalValue,affineD,basePoint,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk]
  ring

theorem nonlinearShift_second (P : Poly) (r : ℂ) :
    planeJet2 r (nonlinearShift P)=affineJet2 r P+
      (r^2/72)*criticalValue r (pderiv Coord.J P) := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  simp [planeJet2,planeValue,nonlinearShift_partial,nonlinearShift_eval,nonlinearB,affineB,
    affineJet2,criticalValue,affineD,basePoint,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,
    partials_commute Coord.J Coord.U]
  ring

theorem nonlinearShift_third (P : Poly) (r : ℂ) :
    planeJet3 r (nonlinearShift P)=affineJet3 r P+
      (r^2/24)*affineJet1 r (pderiv Coord.J P)-
      (7*r^2/72)*criticalValue r (pderiv Coord.J P) := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  simp [planeJet3,planeValue,nonlinearShift_partial,nonlinearShift_eval,nonlinearB,affineB,
    affineJet3,affineJet1,criticalValue,affineD,basePoint,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,
    partials_commute Coord.J Coord.U]
  ring

def nonlinearMinor : Poly := nonlinearShift scaledMinor

theorem nonlinearMinor_zero (r : ℂ) : planeValue r nonlinearMinor=0 := by
  unfold planeValue nonlinearMinor
  rw [nonlinearShift_eval,scaledMinor_zero]
  ring
theorem nonlinearMinor_first (r : ℂ) : planeJet1 r nonlinearMinor=0 := by
  exact (nonlinearShift_first scaledMinor r).trans (affineMinor_first r)
theorem nonlinearMinor_second (r : ℂ) : planeJet2 r nonlinearMinor=2*axisMinorMass := by
  unfold nonlinearMinor
  rw [nonlinearShift_second,affineMinor_second,criticalMinor_J]
  ring

@[simp] theorem planeJet3_add (r : ℂ) (P Q : Poly) :
    planeJet3 r (P+Q)=planeJet3 r P+planeJet3 r Q := by simp [planeJet3,planeValue]
@[simp] theorem planeJet3_mul (r : ℂ) (P Q : Poly) :
    planeJet3 r (P*Q)=planeJet3 r P*planeValue r Q+
      3*planeJet2 r P*planeJet1 r Q+3*planeJet1 r P*planeJet2 r Q+
      planeValue r P*planeJet3 r Q := by
  simp [planeJet3,planeJet2,planeJet1,planeValue,pderiv_mul]
  ring

end
end HTGeometry.ThetaRatioInfinity
