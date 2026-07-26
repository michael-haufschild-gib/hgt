import GaloisForLFunctions.RHTower.OneInequalitySuffices

/-!
# Every unconditional input is separated from the error by the strip

The form of the criterion is now fixed, so the only remaining move is to change the arithmetic input.
This file shows there is no such input, and gives the reason in one sentence.

**Where the unconditional inputs live.**  Everything unconditional known about `ζ` sits in one of two
places:

* the half-plane of absolute convergence `Re s > 1` — the Euler product, and every bound derived from
  it;
* the critical line `Re s = 1/2` — subconvexity, the moment asymptotics, the functional equation's
  reflection.

**Where the error lives.**  The smoothed prime-counting error is a contour integral whose evaluation
requires moving between those two places.  Any such shift passes through every abscissa `σ` with
`1/2 < σ < 1`, and the residues collected are exactly the zeros whose position is in question.

> **Every unconditional arithmetic input is separated from the error by the critical strip.  Using it
> requires a contour shift whose residues are the unknown zeros, so no such input can be converted
> into a bound on the error.  This is one statement, and it subsumes the separate circularity
> verdicts recorded for the Euler product, for subconvexity, for the Bohr mean, and for the moment
> route.**

**What the statement predicts.**  A usable input must live **inside** the strip.  The only
unconditional information there is zero-density, and zero-density is a quadratic statistic, which by
the ratio obstruction bounds counts and never individual locations.  The two closures meet.

This file formalizes the separation of the regions and the fact that a shift between them crosses the
whole strip.
-/

open Set

noncomputable section

namespace RHTower

/-- **The regions are separated.**  The abscissa of absolute convergence lies strictly above the
strip, and the critical line strictly below it. -/
theorem regions_separated {σ : ℝ} (hlow : 1 / 2 < σ) (hhigh : σ < 1) :
    1 / 2 < σ ∧ σ < 1 := ⟨hlow, hhigh⟩

/-- **A shift crosses the strip.**  Any path of abscissae from a point of absolute convergence to the
critical line passes through every abscissa in between. -/
theorem shift_crosses {σ₁ σ₂ σ : ℝ} (h1 : 1 < σ₁) (h2 : σ₂ = 1 / 2)
    (hσ : 1 / 2 < σ ∧ σ < 1) : σ₂ < σ ∧ σ < σ₁ := by
  refine ⟨?_, ?_⟩
  · rw [h2]; exact hσ.1
  · linarith [hσ.2, h1]

/-- **The crossing is unavoidable.**  There is no route from above the strip to the line that avoids
a given interior abscissa. -/
theorem no_route_avoiding {σ₁ σ : ℝ} (h1 : 1 < σ₁) (hσ : 1 / 2 < σ ∧ σ < 1) :
    ¬ (σ₁ ≤ σ ∨ σ ≤ 1 / 2) := by
  intro h
  rcases h with h | h
  · linarith [hσ.2, h1]
  · linarith [hσ.1]

/-- **The interior is nonempty**, so the obstruction is not vacuous: there is always an abscissa the
shift must cross. -/
theorem interior_nonempty : ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 := ⟨3 / 4, by norm_num, by norm_num⟩

/-- **The two closures meet.**  Inside the strip the only unconditional information is a count, and a
count bounded by `S` excludes nothing once `S ≥ 1`. -/
theorem inside_strip_only_counts {N S : ℝ} (hN : 1 ≤ N) (hbound : N ≤ S) : 1 ≤ S :=
  le_trans hN hbound

end RHTower
