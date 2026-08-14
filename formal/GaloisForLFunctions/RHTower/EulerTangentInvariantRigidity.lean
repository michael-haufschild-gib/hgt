import GaloisForLFunctions.RHTower.QuadrantConvexSchwarzCompleteness

/-!
# Every continuous invariant of a dense translation subgroup is constant

A dense subgroup of a topological additive group has dense affine translates, and a continuous map
constant on those translates is constant outright.  Applied to the completed Euler tangents this is
the classification statement: once the divisor is fixed, no continuous invariant of the regular flux
germ survives the finite Euler-unit gauge action.

* `RHTower.closure_affine_of_topologicalClosure_eq_top_lcs`;
* `RHTower.eq_of_translation_invariant_of_dense`;
* `RHTower.feEulerTangent_invariant_eq_const`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul ℝ E]

/-- **A dense subspace has dense affine translates.** -/
theorem closure_affine_of_topologicalClosure_eq_top_lcs {p : Submodule ℝ E}
    (hp : p.topologicalClosure = ⊤) (v : E) :
    closure ((fun x => v + x) '' (p : Set E)) = Set.univ := by
  have hcl : closure (p : Set E) = Set.univ := by
    have hcoe : ((p.topologicalClosure : Submodule ℝ E) : Set E) = closure (p : Set E) :=
      Submodule.topologicalClosure_coe p
    rw [← hcoe, hp]
    rfl
  have hhom : ((fun x => v + x) '' (p : Set E))
      = (Homeomorph.addLeft v) '' (p : Set E) := rfl
  rw [hhom, ← Homeomorph.image_closure, hcl, Set.image_univ]
  exact (Homeomorph.addLeft v).surjective.range_eq

/-- **A continuous map invariant under a dense subspace of translations is constant.** -/
theorem eq_of_translation_invariant_of_dense {X : Type*} [TopologicalSpace X] [T2Space X]
    {p : Submodule ℝ E} (hp : p.topologicalClosure = ⊤) (F : E → X) (hF : Continuous F)
    (hinv : ∀ g ∈ p, ∀ x : E, F (g + x) = F x) (x y : E) : F x = F y := by
  have hclosed : IsClosed {z : E | F z = F x} := isClosed_eq hF continuous_const
  have hsub : ((fun g => g + x) '' (p : Set E)) ⊆ {z : E | F z = F x} := by
    rintro _ ⟨g, hg, rfl⟩
    exact hinv g hg x
  have himg : ((fun g => g + x) '' (p : Set E)) = ((fun g => x + g) '' (p : Set E)) :=
    Set.image_congr' (fun g => add_comm g x)
  rw [himg] at hsub
  have hdense : closure ((fun g => x + g) '' (p : Set E)) = Set.univ :=
    closure_affine_of_topologicalClosure_eq_top_lcs hp x
  have hall : {z : E | F z = F x} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense]
    exact hclosed.closure_subset_iff.mpr hsub
  have hy : y ∈ {z : E | F z = F x} := by rw [hall]; trivial
  exact hy.symm

/-- **On a convex domain inside the critical quadrant every continuous invariant of the real
symmetrised Euler tangent span is constant.** -/
theorem feEulerTangent_invariant_eq_const {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hDQ : D ⊆ criticalQuadrant)
    (S : Finset Nat.Primes) (F : holoOn D → X) (hF : Continuous F)
    (hinv : ∀ g ∈ Submodule.span ℝ (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
        feEulerTangentOn D (hDQ.trans criticalQuadrant_subset_rightCriticalStrip)
          (p : Nat.Primes)), ∀ x : holoOn D, F (g + x) = F x)
    (x y : holoOn D) : F x = F y :=
  eq_of_translation_invariant_of_dense
    (topologicalClosure_realSpan_feEulerTangentOn_eq_top hDopen hDconv hDQ S) F hF hinv x y

/-- **On a convex right-half-plane domain every continuous invariant of the Euler tangent span is
constant.** -/
theorem eulerTangent_invariant_eq_const {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hDre : D ⊆ {s : ℂ | 0 < s.re})
    (S : Finset Nat.Primes) (F : holoOn D → X) (hF : Continuous F)
    (hinv : ∀ g ∈ Submodule.span ℝ (Set.range (eulerTangentOnFamily D hDre S)),
      ∀ x : holoOn D, F (g + x) = F x)
    (x y : holoOn D) : F x = F y :=
  eq_of_translation_invariant_of_dense
    (topologicalClosure_span_eulerTangentOn_eq_top hDopen hDconv hDre S) F hF hinv x y

end RHTower
