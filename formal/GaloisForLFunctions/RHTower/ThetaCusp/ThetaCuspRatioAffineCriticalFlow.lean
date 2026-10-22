import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCriticalMinorSecondJet
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat72 (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

private theorem univ72 : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

def affineB : Poly := C (1/12:ℂ)-C (7/72:ℂ)*X Coord.U
def affineCoord : Coord → Poly
  | .U => X .U
  | .K => X .K
  | .J => X .J+X .K*affineB

def affineShift : Poly →+* Poly := eval₂Hom C affineCoord
@[simp] theorem affineShift_C (c : ℂ) : affineShift (C c)=C c := by simp [affineShift]
@[simp] theorem affineShift_X (i : Coord) : affineShift (X i)=affineCoord i := by simp [affineShift]

theorem affineShift_eval (P : Poly) (h r s : ℂ) :
    eval (basePoint h r s) (affineShift P)=
      eval (basePoint h r (s+r*(1/12-7*h/72))) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,affineShift_X,eval_X,hp]
    congr 1
    cases i <;> simp only [affineCoord,affineB,map_add,map_sub,map_mul,eval_C,eval_X,basePoint] <;> ring

theorem affineShift_U (P : Poly) :
    pderiv Coord.U (affineShift P)=affineShift (pderiv Coord.U P)-
      C (7/72:ℂ)*X Coord.K*affineShift (pderiv Coord.J P) := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  have hk' : Coord.K≠Coord.J := by intro h; cases h
  have hu' : Coord.U≠Coord.J := by intro h; cases h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]; ring
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,map_add,affineShift_X,hp]
    cases i <;> simp [affineCoord,affineB,pderiv_mul,pderiv_X,Pi.single_apply,hk,hj,hk',hu'] <;> ring

theorem affineShift_J (P : Poly) :
    pderiv Coord.J (affineShift P)=affineShift (pderiv Coord.J P) := by
  have hk : Coord.K≠Coord.J := by intro h; cases h
  have hu : Coord.U≠Coord.J := by intro h; cases h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,map_add,affineShift_X,hp]
    cases i <;> simp [affineCoord,affineB,pderiv_mul,pderiv_X,Pi.single_apply,hk,hu]

theorem affineShift_first (P : Poly) (r : ℂ) :
    eval (basePoint 0 r 0) (pderiv Coord.U (affineShift P))=affineJet1 r P := by
  rw [affineShift_U]
  simp [affineShift_eval,affineJet1,criticalValue,affineD,basePoint]
  ring

theorem affineShift_second (P : Poly) (r : ℂ) :
    eval (basePoint 0 r 0) (pderiv Coord.U (pderiv Coord.U (affineShift P)))=affineJet2 r P := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  simp [affineShift_U,pderiv_mul,pderiv_X,Pi.single_apply,hk,
    affineShift_eval,affineJet2,criticalValue,affineD,basePoint]
  ring

def affineField : Coord → Poly
  | .U => affineShift (infinityField .U)
  | .K => affineShift (infinityField .K)
  | .J => affineShift (infinityField .J)-affineB*affineShift (infinityField .K)+
      C (7/72:ℂ)*X .K*affineShift (infinityField .U)

theorem affineField_coord (i : Coord) :
    flow affineField (affineCoord i)=affineShift (infinityField i) := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have huk : Coord.U≠Coord.K := by intro h; cases h
  have hjk : Coord.J≠Coord.K := by intro h; cases h
  cases i <;> simp [flow,univ72,affineCoord,affineField,affineB,
    pderiv_mul,pderiv_X,Pi.single_apply,hku,hju,hkj,huj,huk,hjk] <;> ring

theorem affineShift_flow (P : Poly) :
    flow affineField (affineShift P)=affineShift (flow infinityField P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [flow_C]
  | add p q hp hq => simp only [map_add,flow_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,flow_mul,flow_X,map_add,affineShift_X,hp,affineField_coord]

/-- The only surviving second transverse forcing at the critical affine boundary. -/
theorem affineField_zero (r : ℂ) :
    eval (basePoint 0 r 0) (affineField .U)=0 ∧
    eval (basePoint 0 r 0) (affineField .K)= -108*r ∧
    eval (basePoint 0 r 0) (affineField .J)=0 := by
  norm_num [affineField,affineShift_eval,affineCoord,affineB,infinityField,driftSquare,deficit,speed,basePoint]
  ring

theorem affineField_first_U (r : ℂ) :
    eval (basePoint 0 r 0) (pderiv Coord.U (affineField .U))=0 := by
  rw [affineField,affineShift_first]
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  norm_num [affineJet1,criticalValue,affineD,infinityField,driftSquare,deficit,
    pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hj,huj,hkj,basePoint]

private def affineFieldJNorm : {P : Poly // affineField .J=P} := by
  have he : affineField .J=affineField .J := rfl
  conv at he =>
    rhs
    norm_num [affineField,affineCoord,affineB,infinityField,driftSquare,deficit,speed,map_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem affineField_first_J (r : ℂ) :
    eval (basePoint 0 r 0) (pderiv Coord.U (affineField .J))=0 := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  rw [affineFieldJNorm.property]
  norm_num [affineFieldJNorm,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hj,basePoint]
  ring

theorem affineField_second_J (r : ℂ) :
    eval (basePoint 0 r 0) (pderiv Coord.U (pderiv Coord.U (affineField .J)))=
      -(9/2:ℂ)*r^2 := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  rw [affineFieldJNorm.property]
  norm_num [affineFieldJNorm,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hj,basePoint]
  ring

end
end HTGeometry.ThetaRatioInfinity
