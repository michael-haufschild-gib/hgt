import Mathlib

/-!
# Arithmetic-complement rank conservation

The recurring "arithmetic complement" law of the frequency-budget cards.  For finite-dimensional
subspaces `V` (the prime-frequency span `span_Q{log p : p ≤ N}`) and `W` (the differential-state
carrier `D`) of a common space, the complement `A_N = V / (V ⊓ W)` — realised here as the quotient
`V ⧸ comap V.subtype W` — carries the prime directions missing from `W`:

`dim V ≤ dim (V / (V ⊓ W)) + dim W`,

equivalently `dim A_N ≥ dim V − dim W`.  A prime direction absent from the carrier `W` must reappear
in the complement; it cannot vanish between them.
-/

open Module Submodule

namespace HTGeometry

/-- Arithmetic-complement rank conservation: the dimension of `V` is at most the dimension of its
complement modulo `W` plus the dimension of `W`.  Hence every direction of `V` outside `W` survives
in the complement `V ⧸ (V ⊓ W)`. -/
theorem finrank_le_arithmeticComplement_add {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (V W : Submodule K E) :
    finrank K ↥V ≤ finrank K (↥V ⧸ Submodule.comap V.subtype W) + finrank K ↥W := by
  have hquot := Submodule.finrank_quotient_add_finrank (R := K) (Submodule.comap V.subtype W)
  have hcomap : finrank K ↥(Submodule.comap V.subtype W) ≤ finrank K ↥W := by
    rw [← Submodule.finrank_map_subtype_eq V (Submodule.comap V.subtype W),
      Submodule.map_comap_subtype]
    exact Submodule.finrank_mono inf_le_right
  omega

end HTGeometry
