import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeLogHeight

/-!
# Numerator--denominator Hasse reconstruction for the Deninger prime lattice

A finitely supported signed prime-exponent vector is determined by the prime product of its positive
part and the prime product of its negative part.  This file packages the pair as faithful global
coordinates, detects the zero lattice vector at `(1,1)`, and identifies that multiplicative
triviality with vanishing of the additive prime-log frequency.

The split is a finite-idelic numerator/denominator model.  It can feed Deninger or adelic routes, but
does not identify these coordinates with completed local Brauer invariants.
-/

noncomputable section

namespace RHTower

/-- Prime-exponent lattices are equivalent to their realized numerator/denominator height pairs. -/
noncomputable def deningerHeightSplitHasseEquivRange :
    DeningerPrimeLattice ≃ Set.range deningerHeightSplit :=
  Equiv.ofInjective deningerHeightSplit deningerHeightSplit_injective

@[simp]
theorem deningerHeightSplitHasseEquivRange_apply (m : DeningerPrimeLattice) :
    (deningerHeightSplitHasseEquivRange m : ℕ × ℕ) = deningerHeightSplit m := rfl

/-- Positive and negative prime products jointly reconstruct a signed exponent vector. -/
theorem deningerPrimeLattice_congr_heightSplit_hasse_iff
    (m n : DeningerPrimeLattice) :
    m = n ↔
      (deningerHeightSplit m).1 = (deningerHeightSplit n).1 ∧
      (deningerHeightSplit m).2 = (deningerHeightSplit n).2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hpos, hneg⟩
    apply deningerHeightSplit_injective
    exact Prod.ext hpos hneg

/-- The signed prime lattice is zero exactly at the unit numerator/denominator pair. -/
theorem deningerPrimeLattice_eq_zero_heightSplit_hasse_iff
    (m : DeningerPrimeLattice) :
    m = 0 ↔ deningerHeightSplit m = (1, 1) := by
  constructor
  · rintro rfl
    simp [deningerHeightSplit, GaloisForLFunctions.positivePart,
      GaloisForLFunctions.negativePart, GaloisForLFunctions.primeProduct]
  · intro h
    apply deningerHeightSplit_injective
    calc
      deningerHeightSplit m = (1, 1) := h
      _ = deningerHeightSplit 0 := by
        symm
        simp [deningerHeightSplit, GaloisForLFunctions.positivePart,
          GaloisForLFunctions.negativePart, GaloisForLFunctions.primeProduct]

/-- Multiplicative split triviality is equivalent to additive prime-log frequency zero. -/
theorem deningerHeightSplit_eq_unit_iff_freq_eq_zero
    (m : DeningerPrimeLattice) :
    deningerHeightSplit m = (1, 1) ↔ deningerFreq m = 0 := by
  rw [← deningerPrimeLattice_eq_zero_heightSplit_hasse_iff,
    deningerFreq_eq_zero_iff]

/-- Every nonzero signed exponent vector changes one side of the height split. -/
theorem deningerHeightSplit_component_ne_one_of_ne_zero
    (m : DeningerPrimeLattice) (hm : m ≠ 0) :
    (deningerHeightSplit m).1 ≠ 1 ∨ (deningerHeightSplit m).2 ≠ 1 := by
  by_contra h
  push Not at h
  exact hm ((deningerPrimeLattice_eq_zero_heightSplit_hasse_iff m).2
    (Prod.ext h.1 h.2))

end RHTower
