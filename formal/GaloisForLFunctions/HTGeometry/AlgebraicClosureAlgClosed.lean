import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Relative algebraic closure inside an algebraically closed field

The relative algebraic closure of a field inside an algebraically closed extension is itself
algebraically closed.  This packages the root-descent fact needed to apply the weak
Nullstellensatz over the concrete algebraic numbers inside `ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The relative algebraic closure inside an algebraically closed field is algebraically closed. -/
theorem algebraicClosure_isAlgClosed
    (E L : Type*) [Field E] [Field L] [Algebra E L] [IsAlgClosed L] :
    IsAlgClosed (algebraicClosure E L) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro f hmonic hirr
  let A := algebraicClosure E L
  have hmapMonic : (f.map (algebraMap A L)).Monic := hmonic.map _
  have hdegree : (f.map (algebraMap A L)).degree ≠ 0 := by
    rw [hmonic.degree_map]
    intro hdegree
    exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (f.map (algebraMap A L)) hdegree
  have hyalg : IsAlgebraic A y := by
    refine ⟨f, hmonic.ne_zero, ?_⟩
    change Polynomial.eval₂ (algebraMap A L) y f = 0
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hy
  let a : A := ⟨y, mem_algebraicClosure_of_isAlgebraic hyalg⟩
  refine ⟨a, ?_⟩
  apply (algebraMap A L).injective
  rw [← Polynomial.eval₂_at_apply]
  change Polynomial.eval₂ (algebraMap A L) y f = 0
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hy

end

end GaloisForLFunctions.HTGeometry
