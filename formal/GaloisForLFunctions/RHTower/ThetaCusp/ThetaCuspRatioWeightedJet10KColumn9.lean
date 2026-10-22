import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KGrid
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def weightedJet10KColumn9Clean : {P : Poly //
    (∑ i ∈ Finset.range 17, jet10KCell i 9)=P} := by
  have h : (∑ i ∈ Finset.range 17, jet10KCell i 9)=
      ∑ i ∈ Finset.range 17, jet10KCell i 9 := rfl
  conv at h =>
    rhs
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,jet10KCell,jet10KPiece0,jet10KPiece1,jet10KPiece2,jet10KPiece3,jet10KPiece4,jet10KPiece5,jet10KPiece6,jet10KPiece7,jet10KPiece8,jet10KPiece9,jet10KPiece10,jet10KPiece11,jet10KPiece12,jet10KPiece13,jet10KPiece14,jet10KPiece15,jet10KPiece16]
    dsimp only [jet10KPiece12C9,jet10KPiece12C9Part0,jet10KPiece12Term40,jet10KPiece12Term41,jet10KPiece12Term42,jet10KPiece12Term43,jet10KPiece12Term44,jet10KPiece12Term45,jet10KPiece12Term46,jet10KPiece12Term47,jet10KPiece13C9,jet10KPiece13C9Part0,jet10KPiece13Term23,jet10KPiece13Term24,jet10KPiece13Term25,jet10KPiece13Term26,jet10KPiece13Term27,jet10KPiece13Term28,jet10KPiece13Term29,jet10KPiece13Term30]
    simp
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩
end
end HTGeometry.ThetaRatioWeightedSquare
