import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity
import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian

/-!
# Chronometric rigidity on a bundle of tangent fibers

The polarization argument identifying a symmetric bilinear form from its diagonal values is
fiberwise, so it lifts verbatim from a single model fiber to a family of fibers indexed by the
event set. This file carries out that lift and instantiates it in the two cases the continuum
statement needs:

* the tangent bundle `TangentSpace I x` of a charted smooth manifold;
* a coordinate chart, where a metric field is a smooth nondegenerate symmetric matrix field.

In both cases squared clock intervals determine the metric field, hence the branch-safe
chronometric solution graph of an arbitrary nonlinear gravity law determines the law.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

open scoped BigOperators

/-- **Diagonal values determine a symmetric bilinear form.** This is the polarization identity in
its fiberwise form; no signature, topology or finiteness hypothesis is used. -/
theorem bilinForm_eq_of_diagonal_eq {V : Type v} [AddCommGroup V] [Module ℝ V]
    {B C : LinearMap.BilinForm ℝ V}
    (hB : ∀ u v, B u v = B v u) (hC : ∀ u v, C u v = C v u)
    (hdiag : ∀ v, B v v = C v v) : B = C := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  have hBpol : B u v = (B (u + v) (u + v) - B u u - B v v) / 2 := by
    simp only [map_add, LinearMap.add_apply]
    rw [hB v u]
    ring
  have hCpol : C u v = (C (u + v) (u + v) - C u u - C v v) / 2 := by
    simp only [map_add, LinearMap.add_apply]
    rw [hC v u]
    ring
  rw [hBpol, hCpol, hdiag, hdiag, hdiag]

/-- A chronometric metric field on a bundle of fibers: every event carries a symmetric real
bilinear form on its own tangent fiber. -/
structure BundleChronometricMetric (Event : Type u) (Fiber : Event → Type v)
    [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)] where
  /-- Metric coefficients on the fiber over each event. -/
  form : ∀ x, LinearMap.BilinForm ℝ (Fiber x)
  symmetric : ∀ x u v, form x u v = form x v u

namespace BundleChronometricMetric

variable {Event : Type u} {Fiber : Event → Type v}
  [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)]

@[ext] theorem ext {g h : BundleChronometricMetric Event Fiber}
    (hform : g.form = h.form) : g = h := by
  cases g
  cases h
  simp_all

/-- Signed infinitesimal squared-clock data of a bundle metric field. -/
def squaredInterval (g : BundleChronometricMetric Event Fiber) :
    ∀ x, Fiber x → ℝ :=
  fun x v => g.form x v v

theorem form_eq_half_squaredInterval_polarization
    (g : BundleChronometricMetric Event Fiber) (x : Event) (u v : Fiber x) :
    g.form x u v =
      (g.squaredInterval x (u + v) - g.squaredInterval x u - g.squaredInterval x v) / 2 := by
  simp only [squaredInterval, map_add, LinearMap.add_apply]
  rw [g.symmetric x v u]
  ring

/-- **Squared clock intervals determine the complete bundle metric field.** -/
theorem squaredInterval_injective :
    Function.Injective
      (squaredInterval : BundleChronometricMetric Event Fiber → ∀ x, Fiber x → ℝ) := by
  intro g h heq
  apply ext
  funext x
  refine bilinForm_eq_of_diagonal_eq (g.symmetric x) (h.symmetric x) ?_
  intro v
  exact congrFun (congrFun heq x) v

end BundleChronometricMetric

/-- **Chronometric operator rigidity over a bundle of tangent fibers.** Two arbitrary nonlinear
gravity laws have identical branch-safe squared-clock solution graphs exactly when they are the
same operator. -/
theorem bundleChronometricOperatorRigidity
    {Event : Type u} {Fiber : Event → Type v}
    [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)]
    {Source : Type w}
    (law₁ law₂ : BundleChronometricMetric Event Fiber → Source) :
    chronometricSolutionGraph BundleChronometricMetric.squaredInterval law₁ =
        chronometricSolutionGraph BundleChronometricMetric.squaredInterval law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective
    BundleChronometricMetric.squaredInterval_injective law₁ law₂

/-! ## Tangent bundle of a charted smooth manifold -/

section TangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A chronometric metric field on the tangent bundle of a charted manifold. -/
abbrev TangentChronometricMetric : Type _ :=
  BundleChronometricMetric M (TangentSpace I)

variable {I M}

/-- **Squared clock intervals determine a tangent-bundle metric field.** -/
theorem tangentSquaredInterval_injective :
    Function.Injective
      (BundleChronometricMetric.squaredInterval :
        TangentChronometricMetric I M → ∀ x : M, TangentSpace I x → ℝ) :=
  BundleChronometricMetric.squaredInterval_injective

/-- **Chronometric operator rigidity on the tangent bundle of a charted manifold.** -/
theorem tangentChronometricOperatorRigidity {Source : Type w}
    (law₁ law₂ : TangentChronometricMetric I M → Source) :
    chronometricSolutionGraph BundleChronometricMetric.squaredInterval law₁ =
        chronometricSolutionGraph BundleChronometricMetric.squaredInterval law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective tangentSquaredInterval_injective law₁ law₂

end TangentBundle

/-! ## Coordinate chart: smooth nondegenerate matrix metric fields -/

namespace SmoothPseudoMetric

variable {d : ℕ}

/-- A smooth chart metric is determined by its coefficient field. -/
theorem ext' {g h : SmoothPseudoMetric d} (hmetric : g.metric = h.metric) : g = h := by
  obtain ⟨G, _, _, _⟩ := g
  obtain ⟨G', _, _, _⟩ := h
  have hG : G = G' := hmetric
  subst hG
  rfl

/-- Signed squared clock intervals of a smooth chart metric field. -/
noncomputable def squaredInterval (g : SmoothPseudoMetric d) :
    (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
  fun x v => ∑ i, ∑ j, g.metric x i j * v i * v j

theorem squaredInterval_eq_toBilin' (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) :
    g.squaredInterval x v = Matrix.toBilin' (g.metric x) v v := by
  rw [Matrix.toBilin'_apply]
  simp only [squaredInterval]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem toBilin'_symm (g : SmoothPseudoMetric d) (x : Fin d → ℝ) (u v : Fin d → ℝ) :
    Matrix.toBilin' (g.metric x) u v = Matrix.toBilin' (g.metric x) v u := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hsym : g.metric x j i = g.metric x i j := by
    calc g.metric x j i = (g.metric x).transpose i j := rfl
      _ = g.metric x i j := by rw [g.metric_symm x]
  rw [hsym]
  ring

/-- **Squared clock intervals determine a smooth chart metric field.** -/
theorem squaredInterval_injective :
    Function.Injective (squaredInterval : SmoothPseudoMetric d → _) := by
  intro g h heq
  apply ext'
  funext x
  have hbilin : Matrix.toBilin' (g.metric x) = Matrix.toBilin' (h.metric x) := by
    refine bilinForm_eq_of_diagonal_eq (g.toBilin'_symm x) (h.toBilin'_symm x) ?_
    intro v
    rw [← g.squaredInterval_eq_toBilin', ← h.squaredInterval_eq_toBilin']
    exact congrFun (congrFun heq x) v
  exact (Matrix.toBilin' (R₁ := ℝ) (n := Fin d)).injective hbilin

/-- **Chronometric operator rigidity in a coordinate chart.** -/
theorem chronometricOperatorRigidity {Source : Type w}
    (law₁ law₂ : SmoothPseudoMetric d → Source) :
    chronometricSolutionGraph squaredInterval law₁ =
        chronometricSolutionGraph squaredInterval law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective squaredInterval_injective law₁ law₂

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry
