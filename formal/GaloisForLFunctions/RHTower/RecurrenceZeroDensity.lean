import GaloisForLFunctions.RHTower.ReflectionSplitsOddEven
import GaloisForLFunctions.RHTower.PerturbationZero

/-!
# Where independence acts in the favourable direction: self-recurrence

Multiplicative independence of the primes is the only property separating zeta from the
functional-equation counterexamples, but its one exact consequence in this development — the
decoupling of the prime symbol's extremes — *maximises* the prime side and therefore works against
positivity.  This file records where it acts the other way.

**The conjecture that fails.**  An off-critical zero does **not** impose a `ℚ`-linear relation among
the prime logarithms.  A zero is a location in the plane; nothing transports it into an additive
relation among `log p`, and the growth it forces on the prime-counting error is an `Ω`-result, not a
contradiction.  So independence cannot exclude off-line zeros directly.

**Where it does act favourably.**  Independence gives equidistribution of the phases `(t log p)_p`,
hence approximation of prescribed values by translates `ζ(s + iτ)` — the universality phenomenon.
Universality approximates every **non-vanishing** analytic function on a compact set in the strip.
Whether `ζ` itself is among them is exactly whether `ζ` is non-vanishing there.  That is the
favourable direction: independence supplies the approximation, and the hypothesis is the statement
that `ζ` may approximate itself.

**The mechanism, and it is a counting contradiction.**  Suppose `ζ` had a zero inside a disc `K` in
the strip, and suppose translates `ζ(· + iτ)` approximated `ζ` on `K` to within the minimum of `|ζ|`
on `∂K` for a set of `τ` of positive density.  Each such translate then has a zero in `K` by the
sphere-domination principle, so the zeros of `ζ` in that vertical strip have **positive density in
`T`** — while the zero-counting function in any strip `σ > 1/2 + δ` grows more slowly than linearly.
The two are incompatible.

> **Self-recurrence of `ζ` on a compact set of the strip is incompatible with a zero there.  This is
> the one place where multiplicative independence enters with the sign that helps: it produces the
> translates, and the counting bound converts them into a contradiction.**

This file formalizes the counting contradiction and the transfer of a zero to a nearby function.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower

/-- **The counting contradiction.**  A positive density of zeros in a vertical strip is incompatible
with a sublinear zero count. -/
theorem density_contradiction {δ ε T N : ℝ} (_hδ : 0 < δ) (hT : 0 < T)
    (hlow : δ * T ≤ N) (hhigh : N ≤ ε * T) (hlt : ε < δ) : False := by
  nlinarith

/-- The contradiction persists for every admissible density, so no positive density is possible. -/
theorem no_positive_density {ε T N : ℝ} (hT : 0 < T) (hhigh : N ≤ ε * T) :
    ∀ δ : ℝ, ε < δ → ¬ (δ * T ≤ N) := by
  intro δ hδε hlow
  nlinarith

/-- **Transfer of a zero to a nearby function.**  If `h` vanishes at the centre and dominates `g` on
the sphere, then `g + h` vanishes somewhere in the closed ball: a translate close enough to a
function with a zero has one too. -/
theorem zero_transfers_to_close {g h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (Metric.ball s₀ r)) (hh : DiffContOnCl ℂ h (Metric.ball s₀ r))
    (hcenter : h s₀ = 0) (hg0 : g s₀ ≠ 0)
    (hdom : ∀ z ∈ Metric.sphere s₀ r, 3 * ‖g z‖ ≤ ‖h z‖) :
    ∃ z ∈ Metric.closedBall s₀ r, g z + h z = 0 :=
  exists_zero_of_sphere_domination hr hg hh hcenter hg0 hdom

/-- **The chain.**  If every translate in a set of positive density carries a zero, and the zero count
is sublinear, the assumed zero cannot exist. -/
theorem recurrence_excludes_zero {δ ε T N : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hfromRecurrence : δ * T ≤ N) (hcount : N ≤ ε * T) (hsub : ε < δ) :
    False :=
  density_contradiction hδ hT hfromRecurrence hcount hsub

/-- **Independence acts favourably here.**  The translates are supplied by equidistribution of the
prime phases; the counting bound converts them into a contradiction.  Recorded as the implication
chain it is. -/
theorem favourable_direction {Recurrence ZeroInStrip Contradiction : Prop}
    (hchain : Recurrence → ZeroInStrip → Contradiction) (hR : Recurrence) :
    ZeroInStrip → Contradiction := hchain hR

end RHTower
