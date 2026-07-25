import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The shift groupoid of a reflection-antisymmetric value function

A functional equation `f (c - s) = f s` says exactly one thing about values of the logarithmic
derivative: `L (c - s) = - L s`.  Everything the corpus proves about pairwise translate differences
of a completed L-function follows from that single property, with no analysis left in the argument.

This file isolates it.  For an arbitrary `L : ℂ → ℂ` the oriented differences
`D a b s = L (s + a) - L (s + b)` form a groupoid cocycle — reversal is negation, composition
telescopes, and simultaneous translation of the endpoints is a gauge — unconditionally.  If `L` is
antisymmetric about `c`, then each oriented pair carries its own reflection `s ↦ c - a - b - s`,
and `D a b` is invariant under it.  With a multiplier the invariance acquires a defect which is
again a difference of the same shape, formed from the multiplier's own value function.

Two consequences are pure value relations: `L` vanishes at the reflection centre `c / 2`, and the
antipodal pairs `b = c - a` give even differences.
-/

open Complex

namespace HTGeometry

/-- `L` is antisymmetric about `c`: the shape of `logDeriv f` for `f (c - s) = f s`. -/
def IsReflectionAntisymmetric (c : ℂ) (L : ℂ → ℂ) : Prop := ∀ s, L (c - s) = -L s

/-- `L` is antisymmetric about `c` up to the additive multiplier value function `M`: the shape of
`logDeriv f` for `f (c - s) = m s * f s` with `M = -logDeriv m`. -/
def IsReflectionAntisymmetricWith (c : ℂ) (L M : ℂ → ℂ) : Prop :=
  ∀ s, L (c - s) = -L s + M s

theorem isReflectionAntisymmetricWith_zero {c : ℂ} {L : ℂ → ℂ}
    (hL : IsReflectionAntisymmetric c L) : IsReflectionAntisymmetricWith c L 0 := by
  intro s; simpa using hL s

/-- **A functional equation is exactly antisymmetry of the logarithmic derivative.**  For a
differentiable `f` with `f (c - s) = f s`, the value function `logDeriv f` is antisymmetric about
`c`.  This discharges the interface for every entire function with a reflection functional
equation. -/
theorem isReflectionAntisymmetric_logDeriv {c : ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfe : ∀ s, f (c - s) = f s) :
    IsReflectionAntisymmetric c (logDeriv f) := by
  intro s
  have hcomp : f = f ∘ fun t : ℂ => c - t := funext fun t => (hfe t).symm
  have hg : HasDerivAt (fun t : ℂ => c - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub c
  have h2 := logDeriv_comp (f := f) (hf (c - s)) hg.differentiableAt
  rw [hg.deriv] at h2
  have h1 : logDeriv f s = logDeriv f (c - s) * (-1) := by
    conv_lhs => rw [hcomp]
    exact h2
  linear_combination h1

/-- **The value at the reflection centre vanishes.** -/
theorem eq_zero_of_isReflectionAntisymmetric {c : ℂ} {L : ℂ → ℂ}
    (hL : IsReflectionAntisymmetric c L) : L (c / 2) = 0 := by
  have h := hL (c / 2)
  have hc : c - c / 2 = c / 2 := by ring
  rw [hc] at h
  linear_combination h / 2

/-! ### The shift groupoid -/

/-- The oriented difference of two translates of a value function. -/
def shiftDifference (L : ℂ → ℂ) (a b s : ℂ) : ℂ := L (s + a) - L (s + b)

@[simp]
theorem shiftDifference_self (L : ℂ → ℂ) (a s : ℂ) : shiftDifference L a a s = 0 := by
  simp [shiftDifference]

/-- Reversing an oriented pair negates its value. -/
theorem shiftDifference_swap (L : ℂ → ℂ) (a b s : ℂ) :
    shiftDifference L b a s = -shiftDifference L a b s := by
  simp [shiftDifference]

/-- **The cocycle law.**  Every two-step translate difference telescopes exactly. -/
theorem shiftDifference_cocycle (L : ℂ → ℂ) (a b c s : ℂ) :
    shiftDifference L a c s = shiftDifference L a b s + shiftDifference L b c s := by
  simp [shiftDifference]

/-- **The translation gauge.**  Translating both endpoints and the observation point together does
not change the value. -/
theorem shiftDifference_translationGauge (L : ℂ → ℂ) (a b u s : ℂ) :
    shiftDifference L (a + u) (b + u) (s - u) = shiftDifference L a b s := by
  simp only [shiftDifference]
  ring_nf

/-- The reflection attached to an oriented pair: about the midpoint `(c - a - b) / 2`. -/
def pairReflection (c a b s : ℂ) : ℂ := c - a - b - s

@[simp]
theorem pairReflection_involutive (c a b s : ℂ) :
    pairReflection c a b (pairReflection c a b s) = s := by
  simp [pairReflection]

/-! ### The reflection law -/

/-- **The twisted pair-reflection law.**  Reflecting an oriented difference about its own midpoint
returns the difference minus the difference formed from the multiplier value function. -/
theorem shiftDifference_pairReflection_with {c : ℂ} {L M : ℂ → ℂ}
    (hL : IsReflectionAntisymmetricWith c L M) (a b s : ℂ) :
    shiftDifference L a b (pairReflection c a b s) =
      shiftDifference L a b s - shiftDifference M a b s := by
  have h1 : c - a - b - s + a = c - (s + b) := by ring
  have h2 : c - a - b - s + b = c - (s + a) := by ring
  simp only [shiftDifference, pairReflection, h1, h2, hL (s + b), hL (s + a)]
  ring

/-- **The pair-reflection law.**  For an antisymmetric value function every oriented difference is
invariant under the reflection about its own midpoint.  Every completed-L-function pairwise shift
reflection in the corpus is this statement. -/
theorem shiftDifference_pairReflection {c : ℂ} {L : ℂ → ℂ}
    (hL : IsReflectionAntisymmetric c L) (a b s : ℂ) :
    shiftDifference L a b (pairReflection c a b s) = shiftDifference L a b s := by
  have h := shiftDifference_pairReflection_with (isReflectionAntisymmetricWith_zero hL) a b s
  simpa [shiftDifference] using h

/-- **Antipodal pairs give even differences.**  When the two shifts sum to the reflection constant,
the pair reflection is `s ↦ -s`. -/
theorem shiftDifference_neg_of_add_eq {c : ℂ} {L : ℂ → ℂ}
    (hL : IsReflectionAntisymmetric c L) {a b : ℂ} (hab : a + b = c) (s : ℂ) :
    shiftDifference L a b (-s) = shiftDifference L a b s := by
  have h := shiftDifference_pairReflection hL a b s
  have hrefl : pairReflection c a b s = -s := by
    rw [pairReflection, ← hab]; ring
  rwa [hrefl] at h

/-- The reflected diagonal value relation: the difference at the reflection of the origin equals its
value at the origin. -/
theorem shiftDifference_reflection_origin {c : ℂ} {L : ℂ → ℂ}
    (hL : IsReflectionAntisymmetric c L) (a b : ℂ) :
    shiftDifference L a b (c - a - b) = shiftDifference L a b 0 := by
  have h := shiftDifference_pairReflection hL a b 0
  simpa [pairReflection] using h

end HTGeometry
