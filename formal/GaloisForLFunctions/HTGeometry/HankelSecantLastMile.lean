import GaloisForLFunctions.HTGeometry.KrullDimTrdeg
import GaloisForLFunctions.HTGeometry.ChainDegenerationCohenMacaulay

/-!
# The last mile of the Hankel secant card

```text
isCohenMacaulayRing_hankelSecantQuotient_of_regSeq
    ** a regular sequence of length 2r on the secant quotient makes it Cohen–Macaulay **
```

Both inequalities are already available: the dimension is at most `2r` because the transcendence
degree is (`ringKrullDim_hankelSecantQuotient_le`), and at least `2r` because a ring-regular sequence
bounds the dimension below (`length_le_ringKrullDim_of_isRingRegularSeq`).  The images of the
sequence are ring-regular by `isRingRegularSeq_map_mk`.

So the Cohen–Macaulayness of the secant ring is reduced to exactly one statement: that a regular
sequence of length `2r` exists on it.  That is what the degeneration transports from the chain ring,
where the sequence is already proved to exist.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- **The last mile.**  A regular sequence of length `2r` on the Hankel secant quotient makes it
Cohen–Macaulay: the dimension is at most `2r` by transcendence degree and at least `2r` because a
ring-regular sequence bounds it below. -/
theorem isCohenMacaulayRing_hankelSecantQuotient_of_regSeq (K : Type) [Field K] [CharZero K]
    {N r : ℕ} (hN : 2 * r ≤ N)
    (hseq : ∃ rs : List (MvPolynomial (Fin N) K), rs.length = 2 * r ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r) rs) :
    IsCohenMacaulayRing (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r) := by
  obtain ⟨rs, hlen, hreg⟩ := hseq
  have hring := isRingRegularSeq_map_mk (RHTower.finiteHankelSecantIdeal K N r) rs hreg
  refine ⟨rs.map (Ideal.Quotient.mk _), hring, ?_⟩
  have hge := length_le_ringKrullDim_of_isRingRegularSeq _ hring
  rw [List.length_map, hlen] at hge ⊢
  exact le_antisymm hge (ringKrullDim_hankelSecantQuotient_le K hN)

end GaloisForLFunctions.HTGeometry
