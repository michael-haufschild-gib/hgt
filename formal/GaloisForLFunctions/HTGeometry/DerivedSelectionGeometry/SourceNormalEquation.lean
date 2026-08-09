import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceOrientation

/-!
# The unsquared normal equation of the literal cyclic source

Two complements to the source-orientation theorem:

* `coordSum_srcDefect` — the coordinate sum of the literal source defect is the unsquared normal
  equation `(q-1) c ε(x)`, linear in the wall equation and in the source trace;
* `srcBoundary_eq_antidiagonal_of_eq_one` — at the identity point the two generators of the source
  boundary span the single anti-diagonal line, so the remaining quotient is the coordinate-sum
  orientation line.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [AddCommGroup S] [Module R S]
  {tauS : S →ₗ[R] S} {eps : S →ₗ[R] R} {q c : R}

/-- **(7.3).**  The coordinate sum of the literal source defect is the unsquared normal equation
`(q-1) c ε(x)`. -/
theorem coordSum_srcDefect (hinv : ∀ x, eps (tauS x) = eps x) (x : S) :
    (srcDefect tauS eps q c x).1 + (srcDefect tauS eps q c x).2 = (q - 1) * (c * eps x) := by
  rw [srcDefect_apply hinv x]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Theorem 4A.1, identity fibre.**  At `q = 1` the two generators of the minimal source boundary
span the anti-diagonal line. -/
theorem srcBoundary_eq_antidiagonal_of_eq_one (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hc : IsUnit c) :
    srcBoundary tauS eps (1 : R) c = Submodule.span R {((-1 : R), (1 : R))} := by
  rw [srcBoundary, range_srcDefect hinv heps hc, range_srcRotDefect hinv heps hc]
  have hneg : ((1 : R), (-1 : R)) = -((-1 : R), (1 : R)) := by
    refine Prod.ext ?_ ?_ <;> simp
  have hspan : (Submodule.span R {((1 : R), (-1 : R))} : Submodule R (R × R))
      = Submodule.span R {((-1 : R), (1 : R))} := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
      rw [hneg]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)
    · refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
      have h1 : ((-1 : R), (1 : R)) = -((1 : R), (-1 : R)) := by
        refine Prod.ext ?_ ?_ <;> simp
      rw [h1]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)
  rw [hspan, sup_idem]

end GaloisForLFunctions.HTGeometry.DerivedSelection
