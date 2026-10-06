import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KGrid
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def weightedJet10KColumn7Clean : {P : Poly //
    (∑ i ∈ Finset.range 17, jet10KCell i 7)=P} := by
  have h : (∑ i ∈ Finset.range 17, jet10KCell i 7)=
      ∑ i ∈ Finset.range 17, jet10KCell i 7 := rfl
  conv at h =>
    rhs
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,jet10KCell,jet10KPiece0,jet10KPiece1,jet10KPiece2,jet10KPiece3,jet10KPiece4,jet10KPiece5,jet10KPiece6,jet10KPiece7,jet10KPiece8,jet10KPiece9,jet10KPiece10,jet10KPiece11,jet10KPiece12,jet10KPiece13,jet10KPiece14,jet10KPiece15,jet10KPiece16]
    dsimp only [jet10KPiece9C7,jet10KPiece9C7Part0,jet10KPiece9C7Part1,jet10KPiece9Term54,jet10KPiece9Term55,jet10KPiece9Term56,jet10KPiece9Term57,jet10KPiece9Term58,jet10KPiece9Term59,jet10KPiece9Term60,jet10KPiece9Term61,jet10KPiece9Term62,jet10KPiece9Term63,jet10KPiece9Term64,jet10KPiece9Term65,jet10KPiece9Term66,jet10KPiece10C7,jet10KPiece10C7Part0,jet10KPiece10C7Part1,jet10KPiece10Term50,jet10KPiece10Term51,jet10KPiece10Term52,jet10KPiece10Term53,jet10KPiece10Term54,jet10KPiece10Term55,jet10KPiece10Term56,jet10KPiece10Term57,jet10KPiece10Term58,jet10KPiece10Term59,jet10KPiece10Term60,jet10KPiece10Term61,jet10KPiece10Term62,jet10KPiece11C7,jet10KPiece11C7Part0,jet10KPiece11C7Part1,jet10KPiece11Term30,jet10KPiece11Term31,jet10KPiece11Term32,jet10KPiece11Term33,jet10KPiece11Term34,jet10KPiece11Term35,jet10KPiece11Term36,jet10KPiece11Term37,jet10KPiece11Term38,jet10KPiece11Term39,jet10KPiece11Term40,jet10KPiece11Term41,jet10KPiece11Term42,jet10KPiece11Term43,jet10KPiece11Term44,jet10KPiece11Term45,jet10KPiece11Term46,jet10KPiece11Term47,jet10KPiece12C7,jet10KPiece12C7Part0,jet10KPiece12C7Part1,jet10KPiece12Term12,jet10KPiece12Term13,jet10KPiece12Term14,jet10KPiece12Term15,jet10KPiece12Term16,jet10KPiece12Term17,jet10KPiece12Term18,jet10KPiece12Term19,jet10KPiece12Term20,jet10KPiece12Term21,jet10KPiece12Term22,jet10KPiece12Term23,jet10KPiece12Term24,jet10KPiece12Term25,jet10KPiece13C7,jet10KPiece13C7Part0,jet10KPiece13Term10,jet10KPiece13Term11,jet10KPiece13Term12,jet10KPiece13Term13,jet10KPiece13Term14]
    simp
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩
end
end HTGeometry.ThetaRatioWeightedSquare
