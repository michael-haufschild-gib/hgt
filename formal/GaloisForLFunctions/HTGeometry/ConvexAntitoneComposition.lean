import GaloisForLFunctions.HTGeometry.ConvexProductSameDirection
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Convexity of a decreasing convex function of a concave function

A convex *decreasing* function of a concave function is convex: concavity pushes the inner value up
at a convex combination, the outer function is order-reversing so its value goes down, and the outer
convexity estimate finishes.

Applied to `x ↦ x⁻¹` (convex and decreasing on `(0,∞)`) and to the concave inner functions `√·` and
`t ↦ A + t`, this gives the convexity and monotonicity of the two factors of

```text
1 / ((A + t) √t)      (A ≥ 0, t > 0),
```

and hence — through the same-direction product rule — the convexity of that kernel itself.  It is the
integrand whose midpoint values are the weighted rows of the Hilbert–Hankel kernel.
-/

open Set

namespace GaloisForLFunctions

/-- **A decreasing convex function of a concave function is convex.** -/
theorem ConvexOn.comp_concaveOn_of_antitoneOn {s t : Set ℝ} {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ t f) (hfanti : AntitoneOn f t) (hg : ConcaveOn ℝ s g)
    (hmaps : ∀ x ∈ s, g x ∈ t) :
    ConvexOn ℝ s (fun x => f (g x)) := by
  refine ⟨hg.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hmem : a • x + b • y ∈ s := hg.1 hx hy ha hb hab
  have hgx : g x ∈ t := hmaps x hx
  have hgy : g y ∈ t := hmaps y hy
  have hgc : g (a • x + b • y) ∈ t := hmaps _ hmem
  have hcomb : a • g x + b • g y ∈ t := hf.1 hgx hgy ha hb hab
  have hconc : a • g x + b • g y ≤ g (a • x + b • y) := hg.2 hx hy ha hb hab
  calc f (g (a • x + b • y)) ≤ f (a • g x + b • g y) := hfanti hcomb hgc hconc
    _ ≤ a • f (g x) + b • f (g y) := hf.2 hgx hgy ha hb hab

/-! ## The outer function `x ↦ x⁻¹` -/

/-- The inverse is convex on the positive half-line. -/
theorem convexOn_inv_Ioi : ConvexOn ℝ (Ioi (0:ℝ)) (fun x : ℝ => x⁻¹) := by
  have h := convexOn_zpow (𝕜 := ℝ) (-1)
  simpa using h

/-! ## The inner functions -/

/-- Translation by a constant is concave (indeed affine). -/
theorem concaveOn_const_add {s : Set ℝ} (hs : Convex ℝ s) (A : ℝ) :
    ConcaveOn ℝ s (fun t => A + t) := by
  refine ⟨hs, fun x _ y _ a b ha hb hab => ?_⟩
  have : a • (A + x) + b • (A + y) = A + (a • x + b • y) := by
    simp only [smul_eq_mul]
    have : a * A + b * A = A := by
      rw [← add_mul, hab, one_mul]
    linarith
  exact le_of_eq this

/-! ## The two factors of the Hilbert integrand -/

/-- The shifted inverse `t ↦ (A+t)⁻¹` is convex on the positive half-line for `A ≥ 0`. -/
theorem convexOn_inv_add_const {A : ℝ} (hA : 0 ≤ A) :
    ConvexOn ℝ (Ioi (0:ℝ)) (fun t : ℝ => (A + t)⁻¹) := by
  refine ConvexOn.comp_concaveOn_of_antitoneOn convexOn_inv_Ioi inv_antitoneOn_Ioi
    (concaveOn_const_add (convex_Ioi 0) A) ?_
  intro x hx
  have hx0 : 0 < x := hx
  exact mem_Ioi.mpr (by linarith)

/-- The shifted inverse is decreasing. -/
theorem antitoneOn_inv_add_const {A : ℝ} (hA : 0 ≤ A) :
    AntitoneOn (fun t : ℝ => (A + t)⁻¹) (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have h1 : 0 < A + x := by linarith
  exact inv_anti₀ h1 (by linarith)

/-- The reciprocal square root is convex on the positive half-line. -/
theorem convexOn_inv_sqrt : ConvexOn ℝ (Ioi (0:ℝ)) (fun t : ℝ => (Real.sqrt t)⁻¹) := by
  refine ConvexOn.comp_concaveOn_of_antitoneOn convexOn_inv_Ioi inv_antitoneOn_Ioi
    (Real.strictConcaveOn_sqrt.concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)) ?_
  intro x hx
  exact mem_Ioi.mpr (Real.sqrt_pos.mpr hx)

/-- The reciprocal square root is decreasing. -/
theorem antitoneOn_inv_sqrt : AntitoneOn (fun t : ℝ => (Real.sqrt t)⁻¹) (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  exact inv_anti₀ (Real.sqrt_pos.mpr hx0) (Real.sqrt_le_sqrt hxy)

/-! ## The Hilbert integrand -/

/-- **The kernel `1/((A+t)√t)` is convex on the positive half-line.**  It is the product of the two
positive decreasing convex factors `(A+t)⁻¹` and `(√t)⁻¹`, which vary in the same direction. -/
theorem convexOn_one_div_add_mul_sqrt {A : ℝ} (hA : 0 ≤ A) :
    ConvexOn ℝ (Ioi (0:ℝ)) (fun t : ℝ => 1 / ((A + t) * Real.sqrt t)) := by
  have hrw : (fun t : ℝ => 1 / ((A + t) * Real.sqrt t))
      = fun t : ℝ => (A + t)⁻¹ * (Real.sqrt t)⁻¹ := by
    funext t
    rw [one_div, mul_inv]
  rw [hrw]
  refine ConvexOn.mul_of_sameDirection (convexOn_inv_add_const hA) convexOn_inv_sqrt ?_ ?_
    (sameDirection_of_antitoneOn (antitoneOn_inv_add_const hA) antitoneOn_inv_sqrt)
  · intro x hx
    have hx0 : 0 < x := hx
    have : 0 < A + x := by linarith
    positivity
  · intro x hx
    have hx0 : 0 < x := hx
    have : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    positivity

/-- The kernel is nonnegative on the positive half-line. -/
theorem one_div_add_mul_sqrt_nonneg {A : ℝ} (hA : 0 ≤ A) {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 / ((A + t) * Real.sqrt t) := by
  have h1 : 0 < A + t := by linarith
  have h2 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  positivity

end GaloisForLFunctions
