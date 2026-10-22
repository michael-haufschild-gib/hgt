import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KGrid
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def weightedJet10KColumn8Clean : {P : Poly //
    (∑ i ∈ Finset.range 17, jet10KCell i 8)=P} := by
  have h : (∑ i ∈ Finset.range 17, jet10KCell i 8)=
      ∑ i ∈ Finset.range 17, jet10KCell i 8 := rfl
  conv at h =>
    rhs
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,jet10KCell,jet10KPiece0,jet10KPiece1,jet10KPiece2,jet10KPiece3,jet10KPiece4,jet10KPiece5,jet10KPiece6,jet10KPiece7,jet10KPiece8,jet10KPiece9,jet10KPiece10,jet10KPiece11,jet10KPiece12,jet10KPiece13,jet10KPiece14,jet10KPiece15,jet10KPiece16]
    dsimp only [jet10KPiece10C8,jet10KPiece10C8Part0,jet10KPiece10Term63,jet10KPiece10Term64,jet10KPiece10Term65,jet10KPiece11C8,jet10KPiece11C8Part0,jet10KPiece11Term48,jet10KPiece11Term49,jet10KPiece11Term50,jet10KPiece11Term51,jet10KPiece11Term52,jet10KPiece11Term53,jet10KPiece11Term54,jet10KPiece11Term55,jet10KPiece11Term56,jet10KPiece11Term57,jet10KPiece11Term58,jet10KPiece11Term59,jet10KPiece12C8,jet10KPiece12C8Part0,jet10KPiece12C8Part1,jet10KPiece12Term26,jet10KPiece12Term27,jet10KPiece12Term28,jet10KPiece12Term29,jet10KPiece12Term30,jet10KPiece12Term31,jet10KPiece12Term32,jet10KPiece12Term33,jet10KPiece12Term34,jet10KPiece12Term35,jet10KPiece12Term36,jet10KPiece12Term37,jet10KPiece12Term38,jet10KPiece12Term39,jet10KPiece13C8,jet10KPiece13C8Part0,jet10KPiece13Term15,jet10KPiece13Term16,jet10KPiece13Term17,jet10KPiece13Term18,jet10KPiece13Term19,jet10KPiece13Term20,jet10KPiece13Term21,jet10KPiece13Term22]
    simp
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩
end
end HTGeometry.ThetaRatioWeightedSquare
