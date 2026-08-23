import GaloisForLFunctions.RHTower.PrimeShiftMarcinkiewiczBoundary
import GaloisForLFunctions.RHTower.PrimeShiftMarcinkiewiczLeftBoundary

/-!
# Complete Marcinkiewicz trichotomy for normalized prime shifts

The logarithmic Marcinkiewicz and vanishing-tail memberships distinguish the
three real-part regions of one normalized prime-shift character exactly.
-/

noncomputable section

namespace RHTower

/-- A normalized prime shift belongs to the logarithmic Marcinkiewicz layer
exactly on and to the right of the critical line. -/
theorem memMarcinkiewiczLogLayer_primeShiftCharacter_iff_half_le_re (z : ℂ) :
    MemMarcinkiewiczLogLayer (absField (primeShiftCharacter z)) ↔ 1 / 2 ≤ z.re := by
  constructor
  · intro hmem
    by_contra h
    exact not_memMarcinkiewiczLogLayer_absField_primeShiftCharacter_of_re_lt_half
      (lt_of_not_ge h) hmem
  · intro h
    rcases h.lt_or_eq with hright | hline
    · exact memMarcinkiewiczLogLayer_of_memVanishingTailLayer
        (memVanishingTailLayer_absField_primeShiftCharacter_of_half_lt_re hright)
    · exact memMarcinkiewiczLogLayer_absField_primeShiftCharacter_of_re_eq_half z hline.symm

/-- A normalized prime shift has vanishing Marcinkiewicz tails exactly in the
strict right half-plane. -/
theorem memVanishingTailLayer_primeShiftCharacter_iff_half_lt_re (z : ℂ) :
    MemVanishingTailLayer (absField (primeShiftCharacter z)) ↔ 1 / 2 < z.re := by
  constructor
  · intro htail
    by_contra h
    have hle : z.re ≤ 1 / 2 := le_of_not_gt h
    rcases hle.lt_or_eq with hleft | hline
    · exact not_memMarcinkiewiczLogLayer_absField_primeShiftCharacter_of_re_lt_half hleft
        (memMarcinkiewiczLogLayer_of_memVanishingTailLayer htail)
    · exact not_memVanishingTailLayer_absField_primeShiftCharacter_of_re_eq_half z hline htail
  · exact memVanishingTailLayer_absField_primeShiftCharacter_of_half_lt_re

end RHTower

end
