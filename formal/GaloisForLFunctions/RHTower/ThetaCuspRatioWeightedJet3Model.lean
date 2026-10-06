import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet2Model
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare
private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp
@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
def weightedJetNorm3 : {P : Poly // weightedJet 3=P} := by
  have h : weightedJet 3=weightedJet 3 := rfl
  conv at h =>
    rhs
    rw [weightedJet,weightedJetNorm2.property]
    dsimp only [weightedJetNorm2]
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
