import GaloisForLFunctions.HTGeometry.HalfPlaneGermRing
import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# The unit translation on the germ ring

The unit translation maps the upper right half-plane filter into itself, so precomposition with it
is a ring endomorphism of the germ ring.  On the image of the polynomials it is the substitution
`X ↦ X + 1`, hence on the whole rational function field it is the rational shift: the germ map
intertwines `ratShift` with the translation.

This is the coefficient compatibility that the jet substitution of the shift elimination needs.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- Precomposition with the unit translation, as a ring endomorphism of the germ ring. -/
noncomputable def shiftGerm (σ₀ : ℝ) : HalfPlaneGerm σ₀ →+* HalfPlaneGerm σ₀ where
  toFun g := g.compTendsto (fun s : ℂ => s + 1) (tendsto_add_one_halfPlaneUpper σ₀)
  map_one' := by
    show (1 : HalfPlaneGerm σ₀).compTendsto _ _ = 1
    rfl
  map_mul' g h := by
    induction g using Filter.Germ.inductionOn with
    | h A =>
      induction h using Filter.Germ.inductionOn with
      | h B =>
        rw [← Filter.Germ.coe_mul]
        rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto,
          Filter.Germ.coe_compTendsto, ← Filter.Germ.coe_mul]
        rfl
  map_zero' := by
    show (0 : HalfPlaneGerm σ₀).compTendsto _ _ = 0
    rfl
  map_add' g h := by
    induction g using Filter.Germ.inductionOn with
    | h A =>
      induction h using Filter.Germ.inductionOn with
      | h B =>
        rw [← Filter.Germ.coe_add]
        rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto,
          Filter.Germ.coe_compTendsto, ← Filter.Germ.coe_add]
        rfl

@[simp] theorem shiftGerm_coe (σ₀ : ℝ) (A : ℂ → ℂ) :
    shiftGerm σ₀ (↑A : HalfPlaneGerm σ₀)
      = ((fun s : ℂ => A (s + 1) : ℂ → ℂ) : HalfPlaneGerm σ₀) :=
  Filter.Germ.coe_compTendsto A (tendsto_add_one_halfPlaneUpper σ₀)

/-- On polynomial germs the translation is the substitution `X ↦ X + 1`. -/
theorem shiftGerm_polyGerm (σ₀ : ℝ) (p : Polynomial ℂ) :
    shiftGerm σ₀ (polyGerm σ₀ p)
      = polyGerm σ₀ (p.comp (Polynomial.X + Polynomial.C 1)) := by
  rw [polyGerm_apply, shiftGerm_coe, polyGerm_apply]
  refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun s => ?_)
  simp [Polynomial.eval_comp]

/-- **The germ map intertwines the rational shift with the translation.** -/
theorem shiftGerm_ratGerm (σ₀ : ℝ) (k : RatFunc ℂ) :
    shiftGerm σ₀ (ratGerm σ₀ k) = ratGerm σ₀ (ratShift k) := by
  have hext : ((shiftGerm σ₀).comp (ratGerm σ₀)) = ((ratGerm σ₀).comp ratShift) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ)) ?_
    refine RingHom.ext fun p => ?_
    show shiftGerm σ₀ (ratGerm σ₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p))
      = ratGerm σ₀ (ratShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) p))
    rw [ratGerm_algebraMap, shiftGerm_polyGerm, ratShift_algebraMap, ratGerm_algebraMap]
  exact congrArg (fun f : RatFunc ℂ →+* HalfPlaneGerm σ₀ => f k) hext

/-- Flatness is stable under the translation. -/
theorem IsFlatGerm.shiftGerm {σ₀ : ℝ} {g : HalfPlaneGerm σ₀} (hg : IsFlatGerm σ₀ g) :
    IsFlatGerm σ₀ (shiftGerm σ₀ g) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    have hA : IsFlatOn σ₀ A := hg
    rw [shiftGerm_coe]
    exact hA.shift

end GaloisForLFunctions
