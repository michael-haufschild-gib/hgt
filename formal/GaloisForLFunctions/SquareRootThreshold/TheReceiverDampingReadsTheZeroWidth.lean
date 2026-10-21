import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsALandauExponent
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros

/-!
# The receiver damping reads the zero width

The damped Möbius receiver `E_T(ε) = Σ_{n ≤ T} A_ε(n)²/(n(n+1))` is a one-parameter family in the
damping `ε`, with admissible parameters `receiverDampings` (the dampings with a horizon-uniform
budget). Read as the exponent families of `TheZeroWidthIsALandauExponent` are read, by the set of
admissible parameters, the family measures the zero width from above.

* `zetaZeroWidth_le_of_accPt_receiverDampings`: every accumulation point `ε₀` of the admissible
  dampings satisfies `zetaZeroWidth ≤ ε₀`.
* `Ioi_subset_deficitAbsRates_of_accPt_receiverDampings`: every exponent above such an `ε₀` is an
  admissible exponent of the integrated Chebyshev deficit. The damping family and the deficit
  family are read in one unit.
* `receiverDampingRate`: the infimum of the accumulation points of the admissible dampings. It
  lies in `[zetaZeroWidth, ½]`, and it vanishes iff the admissible dampings accumulate at `0`,
  which is RH (`riemannHypothesis_of_receiverDampingRate_eq_zero`).
* `zetaZeroWidth_le_of_Ioo_subset_receiverDampings`: admissibility on an interval `(a, b)` gives
  `zetaZeroWidth ≤ a`.

Half damping is the trivial rate of the family, where it is bounded unconditionally. The open
direction, `zetaZeroWidth < ε ⟹ ε ∈ receiverDampings`, is admission below half damping. With the
polar ground energy rate, the receiver damping rate is the second family rate that dominates the
width with the converse inequality open.
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

/-! ### The receiver damping rate -/

/-- The receiver damping rate: the infimum of the accumulation points of the admissible
dampings. -/
def receiverDampingRate : ℝ := sInf (derivedSet receiverDampings)

theorem bddBelow_derivedSet_receiverDampings : BddBelow (derivedSet receiverDampings) :=
  ⟨0, fun _ h => nonneg_of_accPt_receiverDampings (mem_derivedSet.mp h)⟩

theorem half_mem_derivedSet_receiverDampings : (1 / 2 : ℝ) ∈ derivedSet receiverDampings :=
  mem_derivedSet.mpr (accPt_receiverDampings_of_half_le le_rfl)

/-- The receiver damping rate dominates the zero width. -/
theorem zetaZeroWidth_le_receiverDampingRate : zetaZeroWidth ≤ receiverDampingRate :=
  le_csInf ⟨_, half_mem_derivedSet_receiverDampings⟩ fun _ h =>
    zetaZeroWidth_le_of_accPt_receiverDampings (mem_derivedSet.mp h)

theorem receiverDampingRate_nonneg : 0 ≤ receiverDampingRate :=
  zetaZeroWidth_nonneg.trans zetaZeroWidth_le_receiverDampingRate

/-- The receiver damping rate is at most the trivial rate `½`. -/
theorem receiverDampingRate_le_half : receiverDampingRate ≤ 1 / 2 :=
  csInf_le bddBelow_derivedSet_receiverDampings half_mem_derivedSet_receiverDampings

/-- The rate vanishes iff the admissible dampings accumulate at `0`: the set of accumulation
points is closed, so its infimum is attained. -/
theorem receiverDampingRate_eq_zero_iff_accPt_zero :
    receiverDampingRate = 0 ↔ AccPt (0 : ℝ) (𝓟 receiverDampings) := by
  constructor
  · intro h
    have hmem : receiverDampingRate ∈ derivedSet receiverDampings :=
      (isClosed_derivedSet receiverDampings).csInf_mem ⟨_, half_mem_derivedSet_receiverDampings⟩
        bddBelow_derivedSet_receiverDampings
    rw [h] at hmem
    exact mem_derivedSet.mp hmem
  · intro h
    exact le_antisymm (csInf_le bddBelow_derivedSet_receiverDampings (mem_derivedSet.mpr h))
      receiverDampingRate_nonneg

/-- A vanishing receiver damping rate is RH. -/
theorem riemannHypothesis_of_receiverDampingRate_eq_zero (h : receiverDampingRate = 0) :
    RiemannHypothesis :=
  riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
    (le_antisymm (zetaZeroWidth_le_receiverDampingRate.trans h.le) zetaZeroWidth_nonneg)

/-- The rate vanishes iff receiver budgets exist at dampings tending to `0`: the cofinal criterion
in the language of the rate. -/
theorem receiverDampingRate_eq_zero_iff_cofinal_budget :
    receiverDampingRate = 0 ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  receiverDampingRate_eq_zero_iff_accPt_zero.trans accPt_zero_receiverDampings_iff

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
