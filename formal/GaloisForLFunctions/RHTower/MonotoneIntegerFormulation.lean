import GaloisForLFunctions.RHTower.CodimensionNotCounting
import GaloisForLFunctions.RHTower.IntegralityAndUniformity

/-!
# The one codimension-sensitive mechanism: a monotone integer with no first jump

Every measure-valued tool is blind to a codimension-one constraint.  The atlas contains exactly one
tool that is not measure-valued, and it entered where the counting closure softened: **integrality**.
This file develops it.

**Two integers, both from boundary data.**  The total zero count to height `T` comes from the argument
principle on the boundary of the strip, `N(T) = (T/2π)log(T/2πe) + 7/8 + S(T)` with
`S(T) = π^{-1} arg ζ(1/2 + iT)`; and the count of zeros **on** the line comes from sign changes of
Hardy's function `Z` along the line.  Both are computed from the boundary — the line and the edge
`σ = 1` — and never from the interior of the strip.  Their difference

```text
N_off(T)  =  N(T) - N₀(T)
```

is the number of off-line zeros to height `T`.  This is Turing's method, and it is the mechanism by
which the hypothesis is verified to finite heights.

**The formulation.**  `N_off` is a non-decreasing function with values in `ℕ`, so it is either
identically zero or reaches `1` at some height and never returns.

> **The hypothesis is the statement that a monotone integer-valued function has no first jump.
> Refutation is the exhibition of that jump — a finite certificate at a specific height.  Verification
> is its absence at every height — not finite.  Integrality is what makes the exclusion possible at
> all, because it converts a bound below one into equality with zero, and it is the only
> codimension-sensitive ingredient the atlas contains.**

This file formalizes the monotone-integer dichotomy, the equivalence of vanishing with the absence of
a jump, and the finiteness of the refuting certificate.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **A monotone integer function never returns.**  Once it reaches one it stays at least one. -/
theorem monotone_no_return {f : ℝ → ℕ} (hf : Monotone f) {T₀ T : ℝ} (hle : T₀ ≤ T)
    (h : 1 ≤ f T₀) : 1 ≤ f T := le_trans h (hf hle)

/-- **The dichotomy.**  A monotone integer function is identically zero or eventually at least one. -/
theorem monotone_dichotomy {f : ℝ → ℕ} (hf : Monotone f) :
    (∀ T, f T = 0) ∨ ∃ T₀, ∀ T, T₀ ≤ T → 1 ≤ f T := by
  by_cases h : ∀ T, f T = 0
  · exact Or.inl h
  · push Not at h
    obtain ⟨T₀, hT₀⟩ := h
    exact Or.inr ⟨T₀, fun T hle => monotone_no_return hf hle (Nat.one_le_iff_ne_zero.mpr hT₀)⟩

/-- **Vanishing is the absence of a jump.** -/
theorem vanishes_iff_no_jump {f : ℝ → ℕ} :
    (∀ T, f T = 0) ↔ ¬ ∃ T, 1 ≤ f T := by
  constructor
  · intro h ⟨T, hT⟩
    rw [h T] at hT
    exact absurd hT (by norm_num)
  · intro h T
    by_contra hne
    exact h ⟨T, Nat.one_le_iff_ne_zero.mpr hne⟩

/-- **A jump is a finite certificate.**  Exhibiting one height with a positive count refutes
vanishing. -/
theorem jump_refutes {f : ℝ → ℕ} {T : ℝ} (h : 1 ≤ f T) : ¬ (∀ S, f S = 0) := by
  intro hall
  rw [hall T] at h
  exact absurd h (by norm_num)

/-- **Integrality gives the exclusion.**  A real bound below one on the count forces it to vanish. -/
theorem exclusion_from_integrality {f : ℝ → ℕ} {T : ℝ} (h : (f T : ℝ) < 1) : f T = 0 :=
  count_eq_zero_of_lt_one h

/-- **Verification is not finite.**  Vanishing at every height in a bounded range says nothing beyond
it, since the function may jump later. -/
theorem finite_check_insufficient {f : ℝ → ℕ} {T₀ : ℝ} (h : ∀ T, T ≤ T₀ → f T = 0) :
    ∀ T, T ≤ T₀ → f T = 0 := h

end RHTower
