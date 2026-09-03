import GaloisForLFunctions.HTGeometry.ComplexPointRationalSmoothPath
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Smooth paths on complex analytifications

The complex analytification of a scheme is covered by analytifications of its affine opens.  This
file records the resulting intrinsic path criterion directly on complex-valued scheme points: a
path is smooth when it is locally contained in every affine chart through the current point and
evaluation of every regular function in that chart is smooth.  The local-containment clause is the
continuity part of the analytification topology; affine regular-function evaluations are its smooth
coordinates.

On an integral scheme this ordinary chartwise definition controls every rational function which
is regular along the path.  The proof is genuinely local: represent the germ at one time by a
section on an open neighbourhood, shrink to an affine open, and use injectivity of every integral
local ring into the function field to identify all other supplied regular germs with that same
section.  No analytification comparison premise is assumed.
-/

namespace AlgebraicGeometry

open CategoryTheory Filter TopologicalSpace
open scoped Topology

noncomputable section

namespace Scheme.ComplexAnalytification

/-- Evaluation of a section in an affine chart, extended by zero away from that chart.  At a point
of the chart this is the literal stalk evaluation of the section's germ.  The value outside the
chart is irrelevant to `ContDiffAt`, because a smooth analytification path remains in the chart on
a neighbourhood of the point under consideration. -/
noncomputable def localSectionValue
    (X : Scheme) (point : ℝ → X.ComplexPoint) (U : X.Opens) (a : Γ(X, U)) (t : ℝ) : ℂ := by
  classical
  exact if h : (point t).center ∈ U then
      (point t).stalkEval (X.presheaf.germ U (point t).center h a)
    else 0

/-- Ordinary smoothness of a path in the complex analytification, expressed in its affine atlas.
The first conjunct is local containment in a chart, hence continuity for the analytification
topology.  The second says that every regular function in that chart is a smooth complex-valued
coordinate along the path. -/
def IsSmoothPath (X : Scheme) (point : ℝ → X.ComplexPoint) : Prop :=
  ∀ (t : ℝ) (U : X.Opens), IsAffineOpen U → (point t).center ∈ U →
    (∀ᶠ u in 𝓝 t, (point u).center ∈ U) ∧
      ∀ a : Γ(X, U), ContDiffAt ℝ ⊤ (localSectionValue X point U a) t

/-- An analytification-smooth path has a continuous path of scheme-theoretic centers. -/
theorem IsSmoothPath.continuous_center
    {X : Scheme} {point : ℝ → X.ComplexPoint} (h : IsSmoothPath X point) :
    Continuous fun t => (point t).center := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_mem_nhds]
  intro t htV
  obtain ⟨_, ⟨U, hU, rfl⟩, htU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open htV hV
  filter_upwards [(h t U hU htU).1] with u hu
  exact hUV hu

/-- On an integral scheme a rational function has at most one regular germ at a given complex
point. -/
theorem _root_.AlgebraicGeometry.Scheme.RationalFunctionRegularAtComplexPoint.germ_eq
    {X : Scheme} [IsIntegral X] {p : X.ComplexPoint} {f : X.functionField}
    (h₁ h₂ : X.RationalFunctionRegularAtComplexPoint p f) : h₁.germ = h₂.germ := by
  apply IsFractionRing.injective (X.presheaf.stalk p.center) X.functionField
  exact h₁.represents.trans h₂.represents.symm

/-- Ordinary affine-chart smoothness on the complex analytification implies smoothness of every
rational observable which is regular along the path. -/
theorem IsSmoothPath.isRationallySmooth
    {X : Scheme} [IsIntegral X] {point : ℝ → X.ComplexPoint}
    (h : IsSmoothPath X point) : Scheme.ComplexPointPath.IsRationallySmooth X point := by
  classical
  intro f regular
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨V, htV, s, hs⟩ := X.presheaf.exists_germ_eq (regular t).germ
  obtain ⟨_, ⟨U, hU, rfl⟩, htU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open htV V.isOpen
  let a : Γ(X, U) := X.presheaf.map (homOfLE hUV).op s
  letI : Nonempty U := ⟨⟨(point t).center, htU⟩⟩
  have hgerm_t :
      X.presheaf.germ U (point t).center htU a = (regular t).germ := by
    rw [← hs]
    exact X.presheaf.germ_res_apply (homOfLE hUV)
      (point t).center htU s
  have ha : X.germToFunctionField U a = f := by
    rw [← X.algebraMap_germ_eq_germToFunctionField htU a]
    change X.presheaf.stalkSpecializes (genericPoint_specializes (point t).center)
      (X.presheaf.germ U (point t).center htU a) = f
    rw [hgerm_t]
    exact (regular t).represents
  obtain ⟨hstay, hsmooth⟩ := h t U hU htU
  apply (hsmooth a).congr_of_eventuallyEq
  filter_upwards [hstay] with u hu
  unfold localSectionValue
  rw [dif_pos hu]
  unfold Scheme.RationalFunctionRegularAtComplexPoint.value
  congr 1
  let sectionRegular : X.RationalFunctionRegularAtComplexPoint (point u) f :=
    { germ := X.presheaf.germ U (point u).center hu a
      represents := by
        change algebraMap (X.presheaf.stalk (point u).center) X.functionField
            (X.presheaf.germ U (point u).center hu a) = f
        rw [X.algebraMap_germ_eq_germToFunctionField hu a]
        exact ha }
  exact Scheme.RationalFunctionRegularAtComplexPoint.germ_eq (regular u) sectionRegular

end Scheme.ComplexAnalytification

end

end AlgebraicGeometry
