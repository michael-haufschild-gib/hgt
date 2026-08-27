import GaloisForLFunctions.HTGeometry.MilnorKTwoSignSubgroup
import GaloisForLFunctions.HTGeometry.MilnorKFiniteField
import GaloisForLFunctions.HTGeometry.MilnorKRationalEntries

/-!
# Characteristic gate for Milnor's sign extension

A nonzero sign symbol `{-1,-1}` can occur only in characteristic zero. In positive
characteristic it descends from the finite prime subfield, whose degree-two Milnor group vanishes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

namespace MilnorDiagonalExtension

/-- **A nonzero `{-1,-1}` symbol forces characteristic zero.** -/
theorem charZero_of_fin4MinusOneSymbol_ne_zero
    (h : fin4MinusOneSymbol F ≠ 0) : CharZero F := by
  rw [← CharP.ringChar_zero_iff_CharZero]
  by_contra hp
  letI : Fact (Nat.Prime (ringChar F)) :=
    ⟨CharP.char_prime_of_ne_zero F hp⟩
  letI : Fintype (⊥ : Subfield F) :=
    Subfield.fintypeBot F (ringChar F)
  let f : (⊥ : Subfield F) →+* F := Subfield.subtype _
  have hzero : fin4MinusOneSymbol (⊥ : Subfield F) = 0 :=
    milnorKDegTwo_eq_zero_of_finite _
  apply h
  have himg := congrArg (milnorKDegMap f 2) hzero
  rw [map_zero] at himg
  have hminus : milnorUnitMap f (-1 : (⊥ : Subfield F)ˣ) = (-1 : Fˣ) := by
    apply Units.ext
    simp [f]
  simpa [fin4MinusOneSymbol, milnorKDegMap_milnorSym2, hminus] using himg

end MilnorDiagonalExtension

end GaloisForLFunctions.HTGeometry
