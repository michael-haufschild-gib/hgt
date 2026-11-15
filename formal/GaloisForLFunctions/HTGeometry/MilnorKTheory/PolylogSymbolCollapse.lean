import GaloisForLFunctions.HTGeometry.MilnorKDegTwoSymbol
import GaloisForLFunctions.HTGeometry.MilnorKGradedRing

/-!
# Classical polylogarithm symbols vanish after the Milnor quotient

The classical symbol from the Goncharov symbol formula has first two entries
`1-a, a`, followed by copies of `a`. Its image in Milnor `K`-theory is zero in every
weight at least two: antisymmetry turns the first pair into a Steinberg relation.
Thus the tensor symbol of a polylogarithm cannot be replaced by a Milnor class.
-/

namespace GaloisForLFunctions.HTGeometry

variable (F : Type*) [Field F]

/-- Admissible classical polylogarithm arguments, excluding zero and one. -/
abbrev PolylogArgument := {a : Fˣ // (a : F) ≠ 1}

/-- The Milnor image of the classical symbol `-[1-a] ⊗ [a] ⊗ ... ⊗ [a]`. -/
noncomputable def classicalPolylogMilnorImage (n : ℕ) (a : PolylogArgument F) :
    MilnorKDeg F (2 + n) :=
  -milnorMul F 2 n (milnorSym2 F (oneSubUnit a.2) a.1)
    (milnorClassDeg F n ⟨List.replicate n a.1, List.length_replicate⟩)

/-- The first two slots already vanish, before any further tensor factors are appended. -/
theorem polylogFirstPair_eq_zero (a : PolylogArgument F) :
    milnorSym2 F (oneSubUnit a.2) a.1 = 0 := by
  rw [milnorSym2_antisymm, milnorSym2_steinberg a.2, neg_zero]

/-- The Milnor quotient annihilates every classical polylogarithm symbol in weight at least two. -/
theorem classicalPolylogMilnorImage_eq_zero (n : ℕ) (a : PolylogArgument F) :
    classicalPolylogMilnorImage F n a = 0 := by
  rw [classicalPolylogMilnorImage, polylogFirstPair_eq_zero, map_zero,
    AddMonoidHom.zero_apply, neg_zero]

end GaloisForLFunctions.HTGeometry
