import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedQuadratic
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare
private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp
@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
def weightedJetNorm0 : {P : Poly // weightedJet 0=P} := by
  have h : weightedJet 0=weightedJet 0 := rfl
  conv at h => rhs; rw [weightedJet]
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
