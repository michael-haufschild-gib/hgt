import GaloisForLFunctions.HTGeometry.GammaShiftShape
import GaloisForLFunctions.HTGeometry.GammaLogStripCollapse

/-!
# The two Gamma comparison orders are inhabited

Shape domination and strict subordination are the lexicographic strict orders that drive the
Gamma asymptotic collapses.  Each is realized outright: a strictly larger degree dominates whatever
the lower data are, and equal Gamma valuations with a strictly larger algebraic exponent are
strictly subordinate.  Both orders are irreflexive, so their laws are not about a degenerate
comparison.
-/

namespace GaloisForLFunctions

namespace HTGeometry

/-- A strictly larger degree dominates. -/
theorem shiftShapeDominates_of_lt {d d' : ℤ} (h : d < d') (ω ω' : ℝ) (b b' : ℤ) :
    ShiftShapeDominates d ω b d' ω' b' := Or.inl h

/-- At equal degree a strictly smaller frequency dominates. -/
theorem shiftShapeDominates_of_omega_lt {d : ℤ} {ω ω' : ℝ} (h : ω' < ω) (b b' : ℤ) :
    ShiftShapeDominates d ω b d ω' b' := Or.inr (Or.inl ⟨rfl, h⟩)

/-- At equal degree and frequency a strictly smaller shift dominates. -/
theorem shiftShapeDominates_of_b_lt {d : ℤ} {ω : ℝ} {b b' : ℤ} (h : b' < b) :
    ShiftShapeDominates d ω b d ω b' := Or.inr (Or.inr ⟨rfl, rfl, h⟩)

/-- Shape domination is irreflexive. -/
theorem not_shiftShapeDominates_self (d : ℤ) (ω : ℝ) (b : ℤ) :
    ¬ ShiftShapeDominates d ω b d ω b := by
  rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩) <;> exact absurd h (lt_irrefl _)

end HTGeometry

/-- **Equal Gamma valuation with a strictly larger algebraic exponent is strictly subordinate.** -/
theorem strictlySubordinateAt_of_a_lt (D : GammaRationalDatum) {a₁ a₂ : ℕ} (h : a₁ < a₂)
    (b₁ b₂ : ℕ) : StrictlySubordinateAt D D a₁ b₁ a₂ b₂ :=
  Or.inr ⟨rfl, Or.inl h⟩

/-- Equal Gamma valuation and exponent with a strictly larger logarithmic exponent is strictly
subordinate. -/
theorem strictlySubordinateAt_of_b_lt (D : GammaRationalDatum) (a : ℕ) {b₁ b₂ : ℕ}
    (h : b₁ < b₂) : StrictlySubordinateAt D D a b₁ a b₂ :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

/-- Strict subordination is irreflexive. -/
theorem not_strictlySubordinateAt_self (D : GammaRationalDatum) (a b : ℕ) :
    ¬ StrictlySubordinateAt D D a b a b := by
  rintro (⟨n, hn, hsum⟩ | ⟨_, (h | ⟨_, h⟩)⟩)
  · omega
  · exact absurd h (lt_irrefl _)
  · exact absurd h (lt_irrefl _)

end GaloisForLFunctions
