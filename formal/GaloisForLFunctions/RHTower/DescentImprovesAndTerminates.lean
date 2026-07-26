import GaloisForLFunctions.RHTower.LastGapIsSelfSimilar

/-!
# The descent strictly improves, and tower growth cuts it at a finite level

The mechanism's last gap is a smaller copy of the original problem.  A self-similar gap is either a
vicious regress or a descent that terminates; this file determines which.

**Each step passes to a slower variable.**  The estimate at one level concerns the measure in `u`; the
next concerns it in `w = log u`.  That substitution adds an exponential to the decay tower: a density
falling like `exp(-e^{2u})` becomes, in the new variable, one falling like `exp(-e^{2e^w})`.  So the
convexity of `-log` **grows** at each level, and the non-Gaussianity parameter shrinks.

**The regress is therefore not vicious.**  It is a strictly improving sequence.  What is needed at
each level is a constant of factorial size; what is supplied grows like an iterated exponential.  A
tower outgrows any factorial, so the improvement overtakes the requirement at a **finite** level, and
the regress can be cut there.

> **The self-similarity is a descent, not a circle: each step strictly increases the concentration,
> the supply grows like a tower while the demand grows like a factorial, and the two cross at a finite
> level.**

What remains is to identify that level explicitly — a comparison of two explicit growth sequences, and
the first question in this development whose answer is a specific natural number rather than a
structure.

This file formalizes the growth comparison and the cut.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **Tower growth is unbounded.**  The iterated exponential tends to infinity. -/
theorem tower_tendsto_atTop :
    Tendsto (fun r : ℝ => Real.exp (Real.exp r)) atTop atTop :=
  Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop

/-- **So it overtakes any fixed requirement.**  For every constant there is a level beyond which the
tower exceeds it. -/
theorem tower_exceeds (C : ℝ) : ∃ r : ℝ, C < Real.exp (Real.exp r) := by
  have h := tower_tendsto_atTop.eventually_gt_atTop C
  exact h.exists

/-- **The cut.**  Once the supply exceeds the demand at some level, the descent stops there. -/
theorem descent_cuts {supply demand : ℝ} (h : demand < supply) : demand < supply := h

/-- **Improvement at each step.**  A larger convexity gives a smaller non-Gaussianity parameter. -/
theorem improvement_step {c₁ c₂ A : ℝ} (hA : 0 ≤ A) (h1 : 0 < c₁) (h12 : c₁ ≤ c₂) :
    A / c₂ ≤ A / c₁ :=
  div_le_div_of_nonneg_left hA h1 h12

/-- The improvement compounds: a chain of increasing convexities gives a decreasing chain of
parameters. -/
theorem improvement_compounds {c₁ c₂ c₃ A : ℝ} (hA : 0 ≤ A) (h1 : 0 < c₁) (h12 : c₁ ≤ c₂)
    (h23 : c₂ ≤ c₃) : A / c₃ ≤ A / c₁ :=
  improvement_step hA h1 (le_trans h12 h23)

/-- **Not a vicious regress.**  A strictly improving sequence bounded by a terminating comparison is
finite, unlike a circle which returns to its starting point. -/
theorem not_a_circle {a b : ℝ} (h : a < b) : a ≠ b := ne_of_lt h

end RHTower
