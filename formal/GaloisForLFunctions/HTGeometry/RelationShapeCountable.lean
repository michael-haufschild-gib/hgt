import Mathlib.Data.Finsupp.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.GDelta.Basic

/-!
# Relation shapes form a countable index

A differential relation is determined, up to its coefficients, by discrete data: the degree in the
spectral variable, the jet depth, the number of expanded monomials, and their exponent vectors.  All
of that is countable.

Since the coefficients are eliminated by the determinant of the expanded evaluation matrix, a Baire
argument has to intersect only countably many residual sets -- one per shape -- and the residual
filter is closed under countable intersections.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

instance instCountableFinsuppFin {n : ℕ} : Countable (Fin n →₀ ℕ) :=
  Countable.of_equiv (Fin n → ℕ) Finsupp.equivFunOnFinite.symm

/-- The discrete data of a differential relation: spectral degree, jet depth, and the exponent
vectors of its expanded monomials. -/
structure RelationShape where
  /-- The degree in the spectral variable. -/
  spectralDegree : ℕ
  /-- The jet depth. -/
  jetDepth : ℕ
  /-- The number of expanded monomials. -/
  monomialCount : ℕ
  /-- The exponent vector of each monomial. -/
  exponent : Fin monomialCount → (Fin jetDepth →₀ ℕ)

/-- The shape data, flattened. -/
def relationShapeEquiv :
    RelationShape ≃ Σ _q : ℕ, Σ n : ℕ, Σ R : ℕ, Fin R → (Fin n →₀ ℕ) where
  toFun S := ⟨S.spectralDegree, S.jetDepth, S.monomialCount, S.exponent⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro p
    obtain ⟨_, _, _, _⟩ := p
    rfl

instance : Countable RelationShape :=
  Countable.of_equiv _ relationShapeEquiv.symm

/-- **A countable family of residual sets has residual intersection.** -/
theorem residual_iInter {α : Type*} [TopologicalSpace α] {ι : Type*} [Countable ι]
    {s : ι → Set α} (h : ∀ i, s i ∈ residual α) : (⋂ i, s i) ∈ residual α :=
  countable_iInter_mem.mpr h

end GaloisForLFunctions.HTGeometry
