import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet8Model
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare
private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp
@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
def weightedJetNorm9 : {P : Poly // weightedJet 9=P} := by
  have h : weightedJet 9=weightedJet 9 := rfl
  conv at h =>
    rhs
    rw [weightedJet,weightedJetNorm8.property]
    dsimp only [weightedJetNorm8]
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
