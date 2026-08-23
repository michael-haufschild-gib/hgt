import Mathlib.Topology.Irreducible
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced

/-!
# Constancy of continuous maps out of irreducible spaces

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §10, the topological
input to Theorem 10.2.

A continuous map from an irreducible space to a Hausdorff space is constant, because its range is
irreducible and an irreducible subset of a Hausdorff space is a subsingleton.

Theorem 10.2 combines this with two further steps, both recorded here: a locally constant map is
constant on preconnected fibres, so it descends along a quotient map onto the base — and the
descended map is continuous, hence constant when the base is irreducible; and a continuous map
into a Hausdorff space is determined by its restriction to a dense subspace, which is the
injectivity of restriction from `X` to the fibre over the generic point.
-/

namespace HTGeometry

open Topology

/-- **A continuous map from an irreducible space to a Hausdorff space is constant.** -/
theorem eq_of_irreducibleSpace {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [IrreducibleSpace Y] [T2Space Z] {f : Y → Z} (hf : Continuous f) (a b : Y) : f a = f b := by
  have h : IsIrreducible (Set.range f) := by
    have := (IrreducibleSpace.isIrreducible_univ Y).image f hf.continuousOn
    rwa [Set.image_univ] at this
  exact h.isPreirreducible.subsingleton ⟨a, rfl⟩ ⟨b, rfl⟩

/-- A continuous map from an irreducible space to a Hausdorff space takes a single value. -/
theorem exists_const_of_irreducibleSpace {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [IrreducibleSpace Y] [T2Space Z] [Nonempty Y] {f : Y → Z} (hf : Continuous f) :
    ∃ c : Z, ∀ y : Y, f y = c :=
  ⟨f (Classical.arbitrary Y), fun y => eq_of_irreducibleSpace hf y _⟩

variable {M Q Z : Type*} [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace Z]

omit [TopologicalSpace Q] [TopologicalSpace Z] in
/-- A locally constant map is constant on the fibres of a map with preconnected fibres. -/
theorem eq_of_isLocallyConstant_of_fibre {r : M → Q} {f : M → Z} (hf : IsLocallyConstant f)
    (hfib : ∀ q : Q, IsPreconnected (r ⁻¹' {q})) {a b : M} (hab : r a = r b) : f a = f b :=
  hf.apply_eq_of_isPreconnected (hfib (r a)) rfl hab.symm

/-- **Deninger, Theorem 10.2.**  A locally constant map whose source fibres over an irreducible
space with preconnected fibres, by a quotient map, is constant: it is constant on the fibres,
hence factors through the base, and the factored map is continuous and therefore constant. -/
theorem eq_of_isQuotientMap_irreducible [IrreducibleSpace Q] [T2Space Z] {r : M → Q}
    (hr : IsQuotientMap r) {f : M → Z} (hf : IsLocallyConstant f)
    (hfib : ∀ q : Q, IsPreconnected (r ⁻¹' {q})) (a b : M) : f a = f b := by
  classical
  set g : Q → Z := f ∘ Function.surjInv hr.surjective with hg
  have hgr : ∀ x : M, g (r x) = f x := by
    intro x
    refine eq_of_isLocallyConstant_of_fibre hf hfib ?_
    exact Function.surjInv_eq hr.surjective (r x)
  have hgcont : Continuous g := by
    rw [hr.continuous_iff]
    have : g ∘ r = f := funext hgr
    rw [this]
    exact hf.continuous
  rw [← hgr a, ← hgr b]
  exact eq_of_irreducibleSpace hgcont (r a) (r b)

/-- **Deninger, Theorem 10.2, the density step.**  Restriction to a dense subspace is injective on
continuous maps into a Hausdorff space. -/
theorem eq_of_dense_eqOn {X : Type*} [TopologicalSpace X] [T2Space Z] {s : Set X}
    (hs : Dense s) {f g : X → Z} (hf : Continuous f) (hg : Continuous g) (h : Set.EqOn f g s) :
    f = g := hf.ext_on hs hg h

end HTGeometry
