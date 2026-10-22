import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Bounded extension off a finite-dimensional subspace

A linear functional prescribed on a finite-dimensional subspace of an inner-product space extends
to a bounded functional on the whole space: the subspace is complete, so it has an orthogonal
projection, and a linear functional on a finite-dimensional space is automatically continuous.

This is the "finite-dimensional Riesz representation and orthogonal extension" step of the
Hilbert--Kummer density argument: prescribed logarithmic moduli on finitely many Kummer classes
are realized by a genuinely bounded functional.

* `deningerFiniteDimExtend` : the extension.
* `deningerFiniteFamilyExtend` : the form used for a finite family of prescribed values.
-/

namespace RHTower

open scoped InnerProductSpace

section FiniteExtension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Bounded extension off a finite-dimensional subspace.**  Every linear functional on a
finite-dimensional subspace is the restriction of a continuous functional on the whole space. -/
theorem deningerFiniteDimExtend (W : Submodule ℝ H) [FiniteDimensional ℝ W]
    (l : W →ₗ[ℝ] ℝ) : ∃ L : H →L[ℝ] ℝ, ∀ w : W, L (w : H) = l w := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  refine ⟨(LinearMap.toContinuousLinearMap l).comp (W.orthogonalProjectionOnto), fun w => ?_⟩
  show (LinearMap.toContinuousLinearMap l) (W.orthogonalProjectionOnto (w : H)) = l w
  rw [W.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

/-- **The finite-family form.**  Values prescribed on a finite family, consistently with a linear
functional on its span, are realized by a bounded functional. -/
theorem deningerFiniteFamilyExtend {n : ℕ} (f : Fin n → H)
    (l : (Submodule.span ℝ (Set.range f)) →ₗ[ℝ] ℝ) :
    ∃ L : H →L[ℝ] ℝ, ∀ i : Fin n, L (f i) = l ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩ := by
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range f)) := by
    refine FiniteDimensional.span_of_finite ℝ ?_
    exact Set.finite_range f
  obtain ⟨L, hL⟩ := deningerFiniteDimExtend (Submodule.span ℝ (Set.range f)) l
  exact ⟨L, fun i => hL ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩⟩

end FiniteExtension

end RHTower
