import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Shifting the variable translates the roots

The Taylor shift of a polynomial is its composition with a translation, so evaluating the shifted
polynomial at a point is evaluating the original at the translated point.

Hence the roots of the shifted polynomial are the roots of the original translated back, and the two
generate the same extension.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem aeval_taylor (r : F) (p : Polynomial F) (x : L) :
    Polynomial.aeval x (Polynomial.taylor r p) =
      Polynomial.aeval (x + algebraMap F L r) p := by
  rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
  congr 1
  simp

/-- **A point is a root of the shift exactly when its translate is a root.** -/
theorem aeval_taylor_eq_zero_iff (r : F) (p : Polynomial F) (x : L) :
    Polynomial.aeval x (Polynomial.taylor r p) = 0 ↔
      Polynomial.aeval (x + algebraMap F L r) p = 0 := by
  rw [aeval_taylor]

theorem taylor_ne_zero {r : F} {p : Polynomial F} (hp : p ≠ 0) :
    Polynomial.taylor r p ≠ 0 := by
  intro hcon
  refine hp ?_
  have h := congrArg (Polynomial.taylor (-r)) hcon
  rwa [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero, map_zero] at h

/-- **The roots of the shift are the roots translated back.** -/
theorem rootSet_taylor (r : F) (p : Polynomial F) (hp : p ≠ 0) :
    (Polynomial.taylor r p).rootSet L =
      (fun x : L => x - algebraMap F L r) '' (p.rootSet L) := by
  have hmapne : ∀ q : Polynomial F, q ≠ 0 → q.map (algebraMap F L) ≠ 0 := by
    intro q hq hcon
    exact hq ((Polynomial.map_eq_zero_iff (algebraMap F L).injective).1 hcon)
  ext x
  rw [Polynomial.mem_rootSet']
  constructor
  · rintro ⟨-, hx⟩
    refine ⟨x + algebraMap F L r, ?_, by ring⟩
    rw [Polynomial.mem_rootSet']
    exact ⟨hmapne p hp, (aeval_taylor_eq_zero_iff r p x).1 hx⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Polynomial.mem_rootSet'] at hy
    refine ⟨hmapne _ (taylor_ne_zero hp), ?_⟩
    rw [aeval_taylor_eq_zero_iff, sub_add_cancel]
    exact hy.2

/-- **The shift does not change the field the roots generate.**  Translating by a base-field element
stays inside the field. -/
theorem adjoin_rootSet_taylor (r : F) (p : Polynomial F) (hp : p ≠ 0) :
    IntermediateField.adjoin F ((Polynomial.taylor r p).rootSet L) =
      IntermediateField.adjoin F (p.rootSet L) := by
  rw [rootSet_taylor r p hp]
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact sub_mem (IntermediateField.subset_adjoin _ _ hy)
      ((IntermediateField.adjoin F (p.rootSet L)).algebraMap_mem r)
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    have h : y = (y - algebraMap F L r) + algebraMap F L r := by ring
    rw [h]
    refine add_mem (IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩) ?_
    exact IntermediateField.algebraMap_mem _ r

end GaloisForLFunctions.HTGeometry
