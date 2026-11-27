import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Mathlib.Data.Fin.Embedding

/-! The successive coordinates of a list of blocks, with their block numbers. -/

namespace GlobalTheory.GLq

variable {g : ℕ}

/-- The index of the block containing a coordinate. -/
def listBlockOf : (L : List (Pc g)) → Fin (degL L) → Fin L.length
  | [], i => Fin.elim0 i
  | _ :: L, i => Fin.addCases (fun _ => 0) (fun j => (listBlockOf L j).succ) i

/-- The embedding of one block's coordinates into the total coordinate space. -/
def listBlockEmbedding : (L : List (Pc g)) → (k : Fin L.length) → Fin (L.get k).1 ↪ Fin (degL L)
  | [], i => Fin.elim0 i
  | p :: L, k => Fin.cases (Fin.castAddEmb (degL L))
      (fun j => (listBlockEmbedding L j).trans (Fin.natAddEmb p.1)) k

@[simp] theorem listBlockOf_left (p : Pc g) (L : List (Pc g)) (i : Fin p.1) :
    listBlockOf (p :: L) (Fin.castAdd (degL L) i) = 0 := by
  change Fin.addCases (m := p.1) (n := degL L) (motive := fun _ => Fin (p :: L).length)
    (fun _ => 0) (fun j => (listBlockOf L j).succ) (Fin.castAdd (degL L) i) = 0
  exact Fin.addCases_left i

@[simp] theorem listBlockOf_right (p : Pc g) (L : List (Pc g)) (j : Fin (degL L)) :
    listBlockOf (p :: L) (Fin.natAdd p.1 j) = (listBlockOf L j).succ := by
  change Fin.addCases (m := p.1) (n := degL L) (motive := fun _ => Fin (p :: L).length)
    (fun _ => 0) (fun j => (listBlockOf L j).succ) (Fin.natAdd p.1 j) = (listBlockOf L j).succ
  exact Fin.addCases_right j

@[simp] theorem listBlockEmbedding_zero (p : Pc g) (L : List (Pc g)) (i : Fin p.1) :
    listBlockEmbedding (p :: L) 0 i = Fin.castAdd (degL L) i := rfl

@[simp] theorem listBlockEmbedding_succ (p : Pc g) (L : List (Pc g)) (k : Fin L.length)
    (i : Fin (L.get k).1) :
    listBlockEmbedding (p :: L) k.succ i = Fin.natAdd p.1 (listBlockEmbedding L k i) := rfl

theorem listBlockOf_mono (L : List (Pc g)) : Monotone (listBlockOf L) := by
  induction L with
  | nil =>
    intro i
    exact Fin.elim0 i
  | cons p L ih =>
    intro i j
    refine Fin.addCases (m := p.1) (n := degL L) (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (m := p.1) (n := degL L) (fun j => ?_) (fun j => ?_) j
    · intro _
      exact ((listBlockOf_left p L i).trans (listBlockOf_left p L j).symm).le
    · intro _
      exact (listBlockOf_left p L i).le.trans (Fin.zero_le _)
    · intro h
      change p.1 + i.val ≤ j.val at h
      exact ((Nat.not_le_of_lt j.isLt) ((Nat.le_add_right p.1 i.val).trans h)).elim
    · intro h
      change p.1 + i.val ≤ p.1 + j.val at h
      have hs : (listBlockOf L i).succ ≤ (listBlockOf L j).succ :=
        Nat.succ_le_succ (ih (Nat.le_of_add_le_add_left h))
      exact (listBlockOf_right p L i).le.trans (hs.trans (listBlockOf_right p L j).symm.le)

/-- Taking the block of an embedded coordinate recovers that block. -/
@[simp] theorem listBlockOf_listBlockEmbedding (L : List (Pc g)) (k : Fin L.length)
    (i : Fin (L.get k).1) : listBlockOf L (listBlockEmbedding L k i) = k := by
  induction L with
  | nil => exact Fin.elim0 k
  | cons p L ih =>
    revert i
    refine Fin.cases ?_ (fun j => ?_) k
    · intro i
      rw [listBlockEmbedding_zero, listBlockOf_left]
    · intro i
      change Fin (L.get j).1 at i
      exact (listBlockOf_right p L (listBlockEmbedding L j i)).trans (congrArg Fin.succ (ih j i))

/-- Every coordinate is obtained from the embedding of its block. -/
theorem exists_listBlockCoordinate (L : List (Pc g)) (i : Fin (degL L)) :
    ∃ j : Fin (L.get (listBlockOf L i)).1, listBlockEmbedding L (listBlockOf L i) j = i := by
  have ofBlock (K : List (Pc g)) (x : Fin (degL K)) (k : Fin K.length)
      (hk : listBlockOf K x = k) (j : Fin (K.get k).1) (hj : listBlockEmbedding K k j = x) :
      ∃ j : Fin (K.get (listBlockOf K x)).1, listBlockEmbedding K (listBlockOf K x) j = x := by
    subst k
    exact ⟨j, hj⟩
  induction L with
  | nil => exact Fin.elim0 i
  | cons p L ih =>
    refine Fin.addCases (m := p.1) (n := degL L) (fun i => ?_) (fun i => ?_) i
    · exact ofBlock (p :: L) (Fin.castAdd (degL L) i) 0 (listBlockOf_left p L i) i rfl
    · obtain ⟨j, hj⟩ := ih i
      exact ofBlock (p :: L) (Fin.natAdd p.1 i) (listBlockOf L i).succ (listBlockOf_right p L i) j
        (congrArg (Fin.natAdd p.1) hj)

end GlobalTheory.GLq
