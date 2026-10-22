import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioIntegerJetTen
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def integerReflection (n : ℕ) : Poly :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:Poly)*(-1:Poly)^(n-i)*integerJet i*integerJet (n-i)

def integerSignedMoment (r : ℕ) : Poly := (-1:Poly)^r*integerReflection (2*r)

def integerThirdMinor : Poly :=
  integerSignedMoment 1*integerSignedMoment 3*integerSignedMoment 5-
  integerSignedMoment 1*(integerSignedMoment 4)^2-
  (integerSignedMoment 2)^2*integerSignedMoment 5+
  2*integerSignedMoment 2*integerSignedMoment 3*integerSignedMoment 4-
  (integerSignedMoment 3)^3

def integerThirdSlope : Poly :=
  integerJet 0*integerLie integerThirdMinor-6*integerThirdMinor*integerLie (integerJet 0)

def reflectionNorm2 : {P : Poly // integerReflection 2=P} := by
  have h : integerReflection 2=integerReflection 2 := rfl
  conv at h =>
    rhs
    norm_num [integerReflection,Finset.sum_range_succ,Nat.choose]
    simp only [jetNorm0.property,jetNorm1.property,jetNorm2.property]
    dsimp only [jetNorm0,jetNorm1,jetNorm2]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def reflectionNorm4 : {P : Poly // integerReflection 4=P} := by
  have h : integerReflection 4=integerReflection 4 := rfl
  conv at h =>
    rhs
    norm_num [integerReflection,Finset.sum_range_succ,Nat.choose]
    simp only [jetNorm0.property,jetNorm1.property,jetNorm2.property,jetNorm3.property,jetNorm4.property]
    dsimp only [jetNorm0,jetNorm1,jetNorm2,jetNorm3,jetNorm4]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def reflectionNorm6 : {P : Poly // integerReflection 6=P} := by
  have h : integerReflection 6=integerReflection 6 := rfl
  conv at h =>
    rhs
    norm_num [integerReflection,Finset.sum_range_succ,Nat.choose]
    simp only [jetNorm0.property,jetNorm1.property,jetNorm2.property,jetNorm3.property,jetNorm4.property,jetNorm5.property,jetNorm6.property]
    dsimp only [jetNorm0,jetNorm1,jetNorm2,jetNorm3,jetNorm4,jetNorm5,jetNorm6]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def reflectionNorm8 : {P : Poly // integerReflection 8=P} := by
  have h : integerReflection 8=integerReflection 8 := rfl
  conv at h =>
    rhs
    norm_num [integerReflection,Finset.sum_range_succ,Nat.choose]
    simp only [jetNorm0.property,jetNorm1.property,jetNorm2.property,jetNorm3.property,jetNorm4.property,jetNorm5.property,jetNorm6.property,jetNorm7.property,jetNorm8.property]
    dsimp only [jetNorm0,jetNorm1,jetNorm2,jetNorm3,jetNorm4,jetNorm5,jetNorm6,jetNorm7,jetNorm8]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
