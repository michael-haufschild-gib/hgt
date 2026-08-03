import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-!
# A product of convex functions varying in the same direction is convex

If `f` and `g` are convex and nonnegative on a convex set and never vary in opposite directions —
`(f x - f y)(g x - g y) ≥ 0` for all `x, y` in the set — then `f · g` is convex there.  Two antitone
factors, or two monotone factors, satisfy the hypothesis.

The computation is exact: after bounding each factor by its convexity estimate, the difference
between the convex combination of the products and the product of the combinations is
`a·b·(f x - f y)(g x - g y)`.

This is what makes a kernel like `1/((A+t)√t)` convex — a product of two positive decreasing convex
factors — which is the hypothesis of the midpoint comparison.
-/

open Set

namespace GaloisForLFunctions

/-- **A product of nonnegative convex factors varying in the same direction is convex.** -/
theorem ConvexOn.mul_of_sameDirection {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hg0 : ∀ x ∈ s, 0 ≤ g x)
    (hdir : ∀ x ∈ s, ∀ y ∈ s, 0 ≤ (f x - f y) * (g x - g y)) :
    ConvexOn ℝ s (fun x => f x * g x) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hfx := hf0 x hx
  have hfy := hf0 y hy
  have hgx := hg0 x hx
  have hgy := hg0 y hy
  have hmem : a • x + b • y ∈ s := hf.1 hx hy ha hb hab
  have hfc : f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
  have hgc : g (a • x + b • y) ≤ a • g x + b • g y := hg.2 hx hy ha hb hab
  have hf0c : 0 ≤ f (a • x + b • y) := hf0 _ hmem
  have hg0c : 0 ≤ g (a • x + b • y) := hg0 _ hmem
  have hprod : f (a • x + b • y) * g (a • x + b • y)
      ≤ (a * f x + b * f y) * (a * g x + b * g y) := by
    simp only [smul_eq_mul] at hfc hgc
    have h1 : 0 ≤ a * g x + b * g y := by positivity
    calc f (a • x + b • y) * g (a • x + b • y)
        ≤ (a * f x + b * f y) * g (a • x + b • y) :=
          mul_le_mul_of_nonneg_right hfc hg0c
      _ ≤ (a * f x + b * f y) * (a * g x + b * g y) := by
          refine mul_le_mul_of_nonneg_left hgc ?_
          positivity
  have hkey : (a * f x + b * f y) * (a * g x + b * g y)
      = (a * (f x * g x) + b * (f y * g y)) - a * b * ((f x - f y) * (g x - g y)) := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    ring
  have hdirxy := hdir x hx y hy
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  simp only [smul_eq_mul]
  calc f (a * x + b * y) * g (a * x + b * y)
      ≤ (a * f x + b * f y) * (a * g x + b * g y) := by
        simpa only [smul_eq_mul] using hprod
    _ = (a * (f x * g x) + b * (f y * g y)) - a * b * ((f x - f y) * (g x - g y)) := hkey
    _ ≤ a * (f x * g x) + b * (f y * g y) := by
        have := mul_nonneg hab0 hdirxy
        linarith

/-- Two antitone nonnegative convex factors never vary in opposite directions. -/
theorem sameDirection_of_antitoneOn {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    ∀ x ∈ s, ∀ y ∈ s, 0 ≤ (f x - f y) * (g x - g y) := by
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · have h1 : f y ≤ f x := hf hx hy hxy
    have h2 : g y ≤ g x := hg hx hy hxy
    have : 0 ≤ (f x - f y) := by linarith
    have : 0 ≤ (g x - g y) := by linarith
    positivity
  · have h1 : f x ≤ f y := hf hy hx hxy
    have h2 : g x ≤ g y := hg hy hx hxy
    nlinarith

end GaloisForLFunctions
