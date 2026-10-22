import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedJet9Balanced
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def jetStep9 (P : Poly) : Poly := squareLie P-6*(9:Poly)*X .K*(9-X .U)*P+X .U*(1-12*X .K)*P
theorem jetStep9_add (P Q : Poly) : jetStep9 (P+Q)=jetStep9 P+jetStep9 Q := by
  unfold jetStep9
  rw [show squareLie (P+Q)=squareLie P+squareLie Q from flow_add squareField P Q]
  ring
private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp
@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

def jetStep9Piece0Norm : {P : Poly // jetStep9 weightedJet9Part0=P} := by
  have h : jetStep9 weightedJet9Part0=jetStep9 weightedJet9Part0 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part0
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece1Norm : {P : Poly // jetStep9 weightedJet9Part1=P} := by
  have h : jetStep9 weightedJet9Part1=jetStep9 weightedJet9Part1 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part1
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece2Norm : {P : Poly // jetStep9 weightedJet9Part2=P} := by
  have h : jetStep9 weightedJet9Part2=jetStep9 weightedJet9Part2 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part2
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece3Norm : {P : Poly // jetStep9 weightedJet9Part3=P} := by
  have h : jetStep9 weightedJet9Part3=jetStep9 weightedJet9Part3 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part3
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece4Norm : {P : Poly // jetStep9 weightedJet9Part4=P} := by
  have h : jetStep9 weightedJet9Part4=jetStep9 weightedJet9Part4 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part4
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece5Norm : {P : Poly // jetStep9 weightedJet9Part5=P} := by
  have h : jetStep9 weightedJet9Part5=jetStep9 weightedJet9Part5 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part5
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece6Norm : {P : Poly // jetStep9 weightedJet9Part6=P} := by
  have h : jetStep9 weightedJet9Part6=jetStep9 weightedJet9Part6 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part6
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece7Norm : {P : Poly // jetStep9 weightedJet9Part7=P} := by
  have h : jetStep9 weightedJet9Part7=jetStep9 weightedJet9Part7 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part7
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece8Norm : {P : Poly // jetStep9 weightedJet9Part8=P} := by
  have h : jetStep9 weightedJet9Part8=jetStep9 weightedJet9Part8 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part8
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece9Norm : {P : Poly // jetStep9 weightedJet9Part9=P} := by
  have h : jetStep9 weightedJet9Part9=jetStep9 weightedJet9Part9 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part9
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece10Norm : {P : Poly // jetStep9 weightedJet9Part10=P} := by
  have h : jetStep9 weightedJet9Part10=jetStep9 weightedJet9Part10 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part10
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece11Norm : {P : Poly // jetStep9 weightedJet9Part11=P} := by
  have h : jetStep9 weightedJet9Part11=jetStep9 weightedJet9Part11 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part11
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece12Norm : {P : Poly // jetStep9 weightedJet9Part12=P} := by
  have h : jetStep9 weightedJet9Part12=jetStep9 weightedJet9Part12 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part12
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece13Norm : {P : Poly // jetStep9 weightedJet9Part13=P} := by
  have h : jetStep9 weightedJet9Part13=jetStep9 weightedJet9Part13 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part13
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece14Norm : {P : Poly // jetStep9 weightedJet9Part14=P} := by
  have h : jetStep9 weightedJet9Part14=jetStep9 weightedJet9Part14 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part14
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece15Norm : {P : Poly // jetStep9 weightedJet9Part15=P} := by
  have h : jetStep9 weightedJet9Part15=jetStep9 weightedJet9Part15 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part15
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def jetStep9Piece16Norm : {P : Poly // jetStep9 weightedJet9Part16=P} := by
  have h : jetStep9 weightedJet9Part16=jetStep9 weightedJet9Part16 := rfl
  conv at h =>
    rhs
    unfold jetStep9 weightedJet9Part16
    simp [squareLie,flow,squareField,univ_eq,pderiv_X,Pi.single_apply,Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩
end
end HTGeometry.ThetaRatioWeightedSquare
