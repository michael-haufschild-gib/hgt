import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece0
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece7
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece9
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece11
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece12
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece13
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece14
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece15
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10KPiece16
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def jet10PieceModel (i : ℕ) : Poly :=
  match i with
  | 0 => jetStep9Piece0Model
  | 1 => jetStep9Piece1Model
  | 2 => jetStep9Piece2Model
  | 3 => jetStep9Piece3Model
  | 4 => jetStep9Piece4Model
  | 5 => jetStep9Piece5Model
  | 6 => jetStep9Piece6Model
  | 7 => jetStep9Piece7Model
  | 8 => jetStep9Piece8Model
  | 9 => jetStep9Piece9Model
  | 10 => jetStep9Piece10Model
  | 11 => jetStep9Piece11Model
  | 12 => jetStep9Piece12Model
  | 13 => jetStep9Piece13Model
  | 14 => jetStep9Piece14Model
  | 15 => jetStep9Piece15Model
  | 16 => jetStep9Piece16Model
  | _ => 0

def jet10KCell (i k : ℕ) : Poly :=
  match i with
  | 0 => jet10KPiece0 k
  | 1 => jet10KPiece1 k
  | 2 => jet10KPiece2 k
  | 3 => jet10KPiece3 k
  | 4 => jet10KPiece4 k
  | 5 => jet10KPiece5 k
  | 6 => jet10KPiece6 k
  | 7 => jet10KPiece7 k
  | 8 => jet10KPiece8 k
  | 9 => jet10KPiece9 k
  | 10 => jet10KPiece10 k
  | 11 => jet10KPiece11 k
  | 12 => jet10KPiece12 k
  | 13 => jet10KPiece13 k
  | 14 => jet10KPiece14 k
  | 15 => jet10KPiece15 k
  | 16 => jet10KPiece16 k
  | _ => 0

theorem weightedJet10_piece_sum : weightedJet 10=
    ∑ i ∈ Finset.range 17, jet10PieceModel i := by
  rw [weightedJet,weightedJet9Balanced_eq]
  change jetStep9 weightedJet9Balanced= _
  simp only [weightedJet9Balanced,jetStep9_add,jetStep9Piece0Model_eq,jetStep9Piece1Model_eq,jetStep9Piece2Model_eq,jetStep9Piece3Model_eq,jetStep9Piece4Model_eq,jetStep9Piece5Model_eq,jetStep9Piece6Model_eq,jetStep9Piece7Model_eq,jetStep9Piece8Model_eq,jetStep9Piece9Model_eq,jetStep9Piece10Model_eq,jetStep9Piece11Model_eq,jetStep9Piece12Model_eq,jetStep9Piece13Model_eq,jetStep9Piece14Model_eq,jetStep9Piece15Model_eq,jetStep9Piece16Model_eq]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,jet10PieceModel]
  simp only [add_assoc,zero_add]

theorem jet10PieceModel_grid (i : ℕ) (hi : i < 17) :
    jet10PieceModel i=∑ k ∈ Finset.range 12, jet10KCell i k := by
  interval_cases i
  · exact jet10KPiece0_eq
  · exact jet10KPiece1_eq
  · exact jet10KPiece2_eq
  · exact jet10KPiece3_eq
  · exact jet10KPiece4_eq
  · exact jet10KPiece5_eq
  · exact jet10KPiece6_eq
  · exact jet10KPiece7_eq
  · exact jet10KPiece8_eq
  · exact jet10KPiece9_eq
  · exact jet10KPiece10_eq
  · exact jet10KPiece11_eq
  · exact jet10KPiece12_eq
  · exact jet10KPiece13_eq
  · exact jet10KPiece14_eq
  · exact jet10KPiece15_eq
  · exact jet10KPiece16_eq

theorem weightedJet10_K_grid : weightedJet 10=
    ∑ k ∈ Finset.range 12, ∑ i ∈ Finset.range 17, jet10KCell i k := by
  rw [weightedJet10_piece_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact jet10PieceModel_grid i (Finset.mem_range.mp hi)
end
end HTGeometry.ThetaRatioWeightedSquare
