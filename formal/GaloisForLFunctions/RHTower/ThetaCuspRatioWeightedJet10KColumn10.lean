import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KGrid
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def weightedJet10KColumn10Clean : {P : Poly //
    (∑ i ∈ Finset.range 17, jet10KCell i 10)=P} := by
  have h : (∑ i ∈ Finset.range 17, jet10KCell i 10)=
      ∑ i ∈ Finset.range 17, jet10KCell i 10 := rfl
  conv at h =>
    rhs
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,jet10KCell,jet10KPiece0,jet10KPiece1,jet10KPiece2,jet10KPiece3,jet10KPiece4,jet10KPiece5,jet10KPiece6,jet10KPiece7,jet10KPiece8,jet10KPiece9,jet10KPiece10,jet10KPiece11,jet10KPiece12,jet10KPiece13,jet10KPiece14,jet10KPiece15,jet10KPiece16]
    dsimp only [jet10KPiece12C10,jet10KPiece12C10Part0,jet10KPiece12Term48,jet10KPiece12Term49,jet10KPiece13C10,jet10KPiece13C10Part0,jet10KPiece13Term31,jet10KPiece13Term32,jet10KPiece13Term33,jet10KPiece13Term34]
    simp
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩
end
end HTGeometry.ThetaRatioWeightedSquare
