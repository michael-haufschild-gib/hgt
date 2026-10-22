import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticSlopeBoundary
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73j (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

def affineJet3 (r : ℂ) (P : Poly) : ℂ :=
  criticalValue r (affineD r (affineD r (affineD r P)))

@[simp] theorem affineJet3_add (r : ℂ) (P Q : Poly) :
    affineJet3 r (P+Q)=affineJet3 r P+affineJet3 r Q := by
  simp [affineJet3,affineD,criticalValue,pderiv_mul]
  ring
@[simp] theorem affineJet3_sub (r : ℂ) (P Q : Poly) :
    affineJet3 r (P-Q)=affineJet3 r P-affineJet3 r Q := by
  simp [affineJet3,affineD,criticalValue,pderiv_mul]
  ring
@[simp] theorem affineJet3_neg (r : ℂ) (P : Poly) :
    affineJet3 r (-P)= -affineJet3 r P := by
  simp [affineJet3,affineD,criticalValue,pderiv_mul]
  ring
@[simp] theorem affineJet3_mul (r : ℂ) (P Q : Poly) :
    affineJet3 r (P*Q)=affineJet3 r P*criticalValue r Q+
      3*affineJet2 r P*affineJet1 r Q+3*affineJet1 r P*affineJet2 r Q+
      criticalValue r P*affineJet3 r Q := by
  simp [affineJet3,affineJet2,affineJet1,affineD,criticalValue,pderiv_mul]
  ring
@[simp] theorem affineJet3_C (r c : ℂ) : affineJet3 r (C c)=0 := by
  simp [affineJet3,affineD,criticalValue]
@[simp] theorem affineJet3_nat (r : ℂ) (n : ℕ) [n.AtLeastTwo] :
    affineJet3 r (ofNat(n) : Poly)=0 := by
  simp [affineJet3,affineD,criticalValue]
@[simp] theorem affineJet3_h (r : ℂ) : affineJet3 r (X Coord.U)=0 := by
  have huj : Coord.U≠Coord.J := by intro h; cases h
  norm_num [affineJet3,affineD,criticalValue,pderiv_X,Pi.single_apply,huj]

end
end HTGeometry.ThetaRatioInfinity
