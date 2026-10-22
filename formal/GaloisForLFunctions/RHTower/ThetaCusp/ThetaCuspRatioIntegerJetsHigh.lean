import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioIntegerJets
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial
private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp
@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
def jetNorm9 : {P : Poly // integerJet 9=P} := by
  have h : integerJet 9=integerJet 9 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm8.property]
    dsimp only [jetNorm8]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
