import GaloisForLFunctions.HTGeometry.NerveMayerVietoris
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The link of a line in the building is the building of the quotient

In the poset of nonzero proper subspaces, the elements strictly above a fixed one correspond, by the
correspondence theorem, to the nonzero proper subspaces of the quotient.  So the link of a vertex of
the building is again a building, of one lower dimension — the induction step that a Solomon--Tits
argument cuts along.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- **The subspaces strictly between a fixed one and the whole space are the nonzero proper subspaces
of the quotient.** -/
def quotientBuildingOrderIso (L : Submodule K V) :
    {S : Submodule K V // L < S ∧ S ≠ ⊤} ≃o {T : Submodule K (V ⧸ L) // T ≠ ⊥ ∧ T ≠ ⊤} where
  toFun S := ⟨Submodule.map L.mkQ S.1, by
      intro hcon
      refine absurd ?_ S.2.1.ne'
      have hle : S.1 ≤ L := by
        intro x hx
        have : L.mkQ x ∈ Submodule.map L.mkQ S.1 := ⟨x, hx, rfl⟩
        rw [hcon, Submodule.mem_bot, ← LinearMap.mem_ker, Submodule.ker_mkQ] at this
        exact this
      exact le_antisymm hle S.2.1.le, by
      intro hcon
      refine S.2.2 ?_
      have : Submodule.comap L.mkQ (Submodule.map L.mkQ S.1) = ⊤ := by rw [hcon, Submodule.comap_top]
      rwa [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 S.2.1.le] at this⟩
  invFun T := ⟨Submodule.comap L.mkQ T.1, by
      refine lt_of_le_of_ne ?_ ?_
      · intro x hx
        have hzero : L.mkQ x = 0 := by
          rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simp [Submodule.mem_comap, hzero]
      · intro hcon
        refine T.2.1 ?_
        have h1 : Submodule.map L.mkQ (Submodule.comap L.mkQ T.1) = T.1 :=
          Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
        have h2 : Submodule.map L.mkQ (Submodule.comap L.mkQ T.1)
            = Submodule.map L.mkQ L := congrArg (Submodule.map L.mkQ) hcon.symm
        rw [h1] at h2
        rw [h2]
        refine le_antisymm ?_ bot_le
        rintro y ⟨x, hx, rfl⟩
        rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hx, by
      intro hcon
      refine T.2.2 ?_
      have := congrArg (Submodule.map L.mkQ) hcon
      rwa [Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top),
        Submodule.map_top, Submodule.range_mkQ] at this⟩
  left_inv S := Subtype.ext (by
    show Submodule.comap L.mkQ (Submodule.map L.mkQ S.1) = S.1
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 S.2.1.le])
  right_inv T := Subtype.ext (by
    show Submodule.map L.mkQ (Submodule.comap L.mkQ T.1) = T.1
    exact Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top))
  map_rel_iff' {S S'} := by
    show Submodule.map L.mkQ S.1 ≤ Submodule.map L.mkQ S'.1 ↔ S.1 ≤ S'.1
    refine ⟨fun h => ?_, fun h => Submodule.map_mono h⟩
    have := Submodule.comap_mono (f := L.mkQ) h
    rwa [Submodule.comap_map_eq, Submodule.comap_map_eq, Submodule.ker_mkQ,
      sup_eq_left.2 S.2.1.le, sup_eq_left.2 S'.2.1.le] at this

/-- **The link of a vertex of the building, as a subtype of the building poset.** -/
def linkEquivStrictlyAbove (L : Submodule K V) (hb : L ≠ ⊥) (ht : L ≠ ⊤) :
    ({q : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} |
        (⟨L, hb, ht⟩ : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) < q} : Type u)
      ≃o {S : Submodule K V // L < S ∧ S ≠ ⊤} where
  toFun q := ⟨q.1.1, q.2, q.1.2.2⟩
  invFun S := ⟨⟨S.1, ne_bot_of_gt (lt_of_le_of_lt bot_le S.2.1), S.2.2⟩, S.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **The link of a vertex of the building is the building of the quotient.** -/
def linkOrderIso (L : Submodule K V) (hb : L ≠ ⊥) (ht : L ≠ ⊤) :
    ({q : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} |
        (⟨L, hb, ht⟩ : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) < q} : Type u)
      ≃o {T : Submodule K (V ⧸ L) // T ≠ ⊥ ∧ T ≠ ⊤} :=
  (linkEquivStrictlyAbove L hb ht).trans (quotientBuildingOrderIso L)

/-- **And therefore has the same order complex.** -/
noncomputable def linkNerveIso (L : Submodule K V) (hb : L ≠ ⊥) (ht : L ≠ ⊤) :
    nerveFunctor.obj (Cat.of ({q : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} |
        (⟨L, hb, ht⟩ : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) < q} : Type u))
      ≅ nerveFunctor.obj (Cat.of {T : Submodule K (V ⧸ L) // T ≠ ⊥ ∧ T ≠ ⊤}) :=
  orderIsoNerveIso (linkOrderIso L hb ht)

end GaloisForLFunctions.HTGeometry
