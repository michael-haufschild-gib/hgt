import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet10PlainPieces
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def jet10KPiece16Term0 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 7 * ((X Coord.K : Poly) ^ Nat.rawCast 1 * Nat.rawCast 147605838209280)

def jet10KPiece16Term1 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 8 * Nat.rawCast 546688289664

def jet10KPiece16Term2 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 8 * ((X Coord.K : Poly) ^ Nat.rawCast 1 * (Int.negOfNat 24629002933248).rawCast)

def jet10KPiece16Term3 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 9 * (Int.negOfNat 4412949120).rawCast

def jet10KPiece16Term4 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 9 * ((X Coord.K : Poly) ^ Nat.rawCast 1 * Nat.rawCast 238299251994)

def jet10KPiece16Term5 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 10 * (Int.negOfNat 1).rawCast

def jet10KPiece16Term6 : Poly := (X Coord.U : Poly) ^ Nat.rawCast 10 * ((X Coord.K : Poly) ^ Nat.rawCast 1 * Nat.rawCast 66)

def jet10KPiece16Term7 : Poly := 0

private theorem jet10KPiece16_model_terms : jetStep9Piece16Model=
    (((jet10KPiece16Term0+jet10KPiece16Term1)+(jet10KPiece16Term2+jet10KPiece16Term3))+((jet10KPiece16Term4+jet10KPiece16Term5)+(jet10KPiece16Term6+jet10KPiece16Term7))) := by rfl

def jet10KPiece16C0Part0 : Poly := ((jet10KPiece16Term1+jet10KPiece16Term3)+(jet10KPiece16Term5+jet10KPiece16Term7))

def jet10KPiece16C0 : Poly := jet10KPiece16C0Part0

def jet10KPiece16C1Part0 : Poly := ((jet10KPiece16Term0+jet10KPiece16Term2)+(jet10KPiece16Term4+jet10KPiece16Term6))

def jet10KPiece16C1 : Poly := jet10KPiece16C1Part0

def jet10KPiece16 : ℕ → Poly
  | 0 => jet10KPiece16C0
  | 1 => jet10KPiece16C1
  | _ => 0

private theorem jet10KPiece16_regroup (f0 f1 f2 f3 f4 f5 f6 f7 : Poly) :
    (((f0+f1)+(f2+f3))+((f4+f5)+(f6+f7)))=((((((((((((0+((f1+f3)+(f5+f7)))+((f0+f2)+(f4+f6)))+0)+0)+0)+0)+0)+0)+0)+0)+0)+0) := by
  simp only [zero_add,add_zero]
  ac_rfl

theorem jet10KPiece16_eq : jetStep9Piece16Model=
    ∑ k ∈ Finset.range 12, jet10KPiece16 k := by
  rw [jet10KPiece16_model_terms]
  have he := jet10KPiece16_regroup jet10KPiece16Term0 jet10KPiece16Term1 jet10KPiece16Term2 jet10KPiece16Term3 jet10KPiece16Term4 jet10KPiece16Term5 jet10KPiece16Term6 jet10KPiece16Term7
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,jet10KPiece16,
    jet10KPiece16C0,jet10KPiece16C0Part0,jet10KPiece16C1,jet10KPiece16C1Part0] using he
end
end HTGeometry.ThetaRatioWeightedSquare
