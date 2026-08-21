import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Tower

/-!
# A subfield inside a fixed field is the whole fixed field once the degree matches

Artin's theorem computes the degree of a field over the fixed field of a finite faithful group
action.  So a subfield contained in that fixed field, over which the degree is already the order of
the group, has nothing left to gain: the intermediate degree is one, and the subfield is the fixed
field.

This is the field-theoretic half of a "finite étale Galois description": once one knows that a
pullback lands inside the invariants of the deck group and that its degree is the degree of the
cover, the pullback *is* the invariant field.

* `eq_fixedPoints_subfield_of_finrank`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The degree criterion.**  A subfield inside the fixed field of a finite faithful action, over
which the whole field already has degree the order of the group, is the fixed field. -/
theorem eq_fixedPoints_subfield_of_finrank
    {K : Type*} [Field K] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G K]
    [FaithfulSMul G K] (L : Subfield K)
    (hle : L ≤ FixedPoints.subfield G K)
    [FiniteDimensional L K]
    (hdeg : Module.finrank L K = Fintype.card G) :
    L = FixedPoints.subfield G K := by
  set M : Subfield K := FixedPoints.subfield G K with hM
  letI : Algebra L M := (Subring.inclusion (by exact_mod_cast hle : L.toSubring ≤ M.toSubring)).toAlgebra
  haveI : IsScalarTower L M K := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : FiniteDimensional L M := by
    refine FiniteDimensional.left L M K
  have hMK : Module.finrank M K = Fintype.card G := FixedPoints.finrank_eq_card G K
  have hmul : Module.finrank L M * Module.finrank M K = Module.finrank L K :=
    Module.finrank_mul_finrank L M K
  rw [hMK, hdeg] at hmul
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hone : Module.finrank L M = 1 :=
    Nat.eq_of_mul_eq_mul_right hcard (by rw [one_mul]; exact hmul)
  have hsub : M ≤ L := by
    intro x hx
    have hspan : Submodule.span L {(1 : M)} = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton (one_ne_zero), hone]
    have hxm : (⟨x, hx⟩ : M) ∈ Submodule.span L {(1 : M)} := by
      rw [hspan]
      trivial
    rw [Submodule.mem_span_singleton] at hxm
    obtain ⟨a, ha⟩ := hxm
    have hthis := congrArg (Subtype.val : M → K) ha
    simp only [Algebra.smul_def, mul_one] at hthis
    have hval : ((a : L) : K) = x := hthis
    rw [← hval]
    exact a.2
  exact le_antisymm hle hsub

end GaloisForLFunctions.HTGeometry
