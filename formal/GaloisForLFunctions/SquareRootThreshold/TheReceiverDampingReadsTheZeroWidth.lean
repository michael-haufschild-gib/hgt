import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsALandauExponent
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros

/-!
# The receiver damping reads the zero width

The damped Möbius receiver `E_T(ε) = Σ_{n ≤ T} A_ε(n)²/(n(n+1))` is a one-parameter family in the
damping `ε`, with admissible parameters `receiverDampings` (the dampings with a horizon-uniform
budget) and rate `receiverDampingRate` (the infimum of their accumulation points). Read as the
exponent families of `TheZeroWidthIsALandauExponent` are read, the family measures the zero width
from above.

* `zetaZeroWidth_le_of_accPt_receiverDampings`: every accumulation point `ε₀` of the admissible
  dampings satisfies `zetaZeroWidth ≤ ε₀`.
* `Ioi_subset_deficitAbsRates_of_accPt_receiverDampings`: every exponent above such an `ε₀` is an
  admissible exponent of the integrated Chebyshev deficit. The damping family and the deficit
  family are read in one unit.
* `zetaZeroWidth_le_receiverDampingRate`: the rate lies in `[zetaZeroWidth, ½]`, and it vanishes
  iff the admissible dampings accumulate at `0`, which is RH.
* `zetaZeroWidth_le_of_Ioo_subset_receiverDampings`: admissibility on an interval `(a, b)` gives
  `zetaZeroWidth ≤ a`.

Half damping is the trivial rate of the family, where it is bounded unconditionally. The open
direction, `zetaZeroWidth < ε ⟹ ε ∈ receiverDampings`, is admission below half damping; the
elementary partial arrow `receiverDampingRate ≤ ¼ + zetaZeroWidth/2` is
`receiverDampingRate_le_half_zetaZeroAbscissa`. With the polar ground energy rate, the receiver
damping rate is the second family rate that dominates the width with the converse inequality open.
-/

open Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Accumulating dampings bound the width.** -/
theorem zetaZeroWidth_le_of_accPt_receiverDampings {ε₀ : ℝ}
    (h : AccPt ε₀ (𝓟 receiverDampings)) : zetaZeroWidth ≤ ε₀ := by
  rw [zetaZeroWidth_le_iff_re_le (nonneg_of_accPt_receiverDampings h)]
  intro ρ hρ
  obtain ⟨hzero, -, hρ1⟩ := (show IsNontrivialZero ρ from hρ)
  exact re_le_of_accPt_receiverDampings h hzero hρ1

/-- Every exponent above an accumulation point of the admissible dampings is an admissible
exponent of the integrated Chebyshev deficit. -/
theorem Ioi_subset_deficitAbsRates_of_accPt_receiverDampings {ε₀ : ℝ}
    (h : AccPt ε₀ (𝓟 receiverDampings)) : Ioi ε₀ ⊆ deficitAbsRates := fun _ hβ =>
  mem_deficitAbsRates_of_lt ((zetaZeroWidth_le_of_accPt_receiverDampings h).trans_lt hβ)

/-- Admissibility on an interval `(a, b)` bounds the width by `a`. -/
theorem zetaZeroWidth_le_of_Ioo_subset_receiverDampings {a b : ℝ} (hab : a < b)
    (h : Ioo a b ⊆ receiverDampings) : zetaZeroWidth ≤ a :=
  zetaZeroWidth_le_of_accPt_receiverDampings (accPt_of_Ioo_subset hab h)

/-- The receiver damping rate dominates the zero width. -/
theorem zetaZeroWidth_le_receiverDampingRate : zetaZeroWidth ≤ receiverDampingRate := by
  rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  linarith [zetaZeroAbscissa_le_half_add_receiverDampingRate]

/-- A vanishing receiver damping rate is RH, in the language of the width. -/
theorem zetaZeroWidth_eq_zero_of_receiverDampingRate_eq_zero (h : receiverDampingRate = 0) :
    zetaZeroWidth = 0 :=
  le_antisymm (zetaZeroWidth_le_receiverDampingRate.trans h.le) zetaZeroWidth_nonneg

/-- **The damping reads the width.** Half damping is admissible and is an accumulation point;
every accumulation point of the admissible dampings bounds the width and every exponent above it
is an admissible deficit exponent; the rate lies in `[zetaZeroWidth, ½]` and vanishes only with
RH. -/
theorem receiver_damping_reads_the_zero_width :
    Ici (1 / 2 : ℝ) ⊆ receiverDampings ∧
    (1 / 2 : ℝ) ∈ derivedSet receiverDampings ∧
    (∀ ε₀ : ℝ, AccPt ε₀ (𝓟 receiverDampings) →
      zetaZeroWidth ≤ ε₀ ∧ Ioi ε₀ ⊆ deficitAbsRates) ∧
    zetaZeroWidth ≤ receiverDampingRate ∧ receiverDampingRate ≤ 1 / 2 ∧
    (receiverDampingRate = 0 → RiemannHypothesis) :=
  ⟨Ici_half_subset_receiverDampings, half_mem_derivedSet_receiverDampings,
    fun _ h => ⟨zetaZeroWidth_le_of_accPt_receiverDampings h,
      Ioi_subset_deficitAbsRates_of_accPt_receiverDampings h⟩,
    zetaZeroWidth_le_receiverDampingRate, receiverDampingRate_le_half,
    riemannHypothesis_of_receiverDampingRate_eq_zero⟩

end GaloisForLFunctions.SquareRootThreshold
