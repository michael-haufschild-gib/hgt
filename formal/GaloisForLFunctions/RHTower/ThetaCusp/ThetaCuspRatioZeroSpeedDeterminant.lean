import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioZeroSpeedFace
/-! # Exact algebra for the zero-defect, zero-speed source-slope face. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

private def detDerivative (a b c d e A B C D E : ℂ) : ℂ :=
  -A*c*e-a*C*e-a*c*E+A*d^2+2*a*d*D+2*b*B*e+b^2*E-
    2*B*c*d-2*b*C*d-2*b*c*D+3*c^2*C

def zeroSpeedMinorPartial (k : ℂ) (hk : k≠0) : ℂ :=
  detDerivative (zeroSpeedValue2 k hk).val (zeroSpeedValue4 k hk).val
    (zeroSpeedValue6 k hk).val (zeroSpeedValue8 k hk).val (zeroSpeedValue10 k hk).val
    (zeroSpeedPartial2 k hk).val (zeroSpeedPartial4 k hk).val
    (zeroSpeedPartial6 k hk).val (zeroSpeedPartial8 k hk).val (zeroSpeedPartial10 k hk).val

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

theorem zeroSpeedMinorPartial_eq (k : ℂ) (hk : k≠0) :
    k^18*eval (slicePoint (9-6/k-4/k^2) k) (pderiv Coord.U zeroDefectMinor)=
      zeroSpeedMinorPartial k hk := by
  let v := slicePoint (9-6/k-4/k^2) k
  have he : k^18*eval v (pderiv Coord.U zeroDefectMinor)=
      detDerivative (k^2*eval v zeroDefectPoly2) (k^4*eval v zeroDefectPoly4)
        (k^6*eval v zeroDefectPoly6) (k^8*eval v zeroDefectPoly8)
        (k^10*eval v zeroDefectPoly10)
        (k^2*eval v (pderiv Coord.U zeroDefectPoly2))
        (k^4*eval v (pderiv Coord.U zeroDefectPoly4))
        (k^6*eval v (pderiv Coord.U zeroDefectPoly6))
        (k^8*eval v (pderiv Coord.U zeroDefectPoly8))
        (k^10*eval v (pderiv Coord.U zeroDefectPoly10)) := by
    simp only [zeroDefectMinor,detDerivative,map_add,map_sub,pderiv_mul,pderiv_pow,
      map_neg,pd_ofNat,zero_mul,zero_add,map_mul,map_pow,map_ofNat,map_natCast]
    ring
  dsimp only [v] at he
  rw [(zeroSpeedValue2 k hk).property,(zeroSpeedValue4 k hk).property,
    (zeroSpeedValue6 k hk).property,(zeroSpeedValue8 k hk).property,
    (zeroSpeedValue10 k hk).property,(zeroSpeedPartial2 k hk).property,
    (zeroSpeedPartial4 k hk).property,(zeroSpeedPartial6 k hk).property,
    (zeroSpeedPartial8 k hk).property,(zeroSpeedPartial10 k hk).property] at he
  exact he

def zeroSpeedMinorPartialNorm (k : ℂ) (hk : k≠0) :
    {a : ℂ // zeroSpeedMinorPartial k hk=a} := by
  have h : zeroSpeedMinorPartial k hk=zeroSpeedMinorPartial k hk := rfl
  conv at h =>
    rhs
    dsimp only [zeroSpeedMinorPartial,detDerivative,
      zeroSpeedValue2,zeroSpeedValue4,zeroSpeedValue6,zeroSpeedValue8,zeroSpeedValue10,
      zeroSpeedPartial2,zeroSpeedPartial4,zeroSpeedPartial6,zeroSpeedPartial8,zeroSpeedPartial10]
    ring_nf
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
