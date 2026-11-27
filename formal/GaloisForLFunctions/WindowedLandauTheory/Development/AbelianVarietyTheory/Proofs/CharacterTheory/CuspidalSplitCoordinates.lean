import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalRadicalReindex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices

/-! A split of the coordinates of one Levi block gives a proper radical
supported on entries from the first part to the second part. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b n : ℕ} [Fact g.Prime]

/-- Enumerate a nontrivial subset first, followed by its complement. -/
theorem exists_fin_split (p : Fin n → Prop) (hp : ∃ i, p i) (hn : ∃ i, ¬ p i) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ e : Fin (a + b) ≃ Fin n,
      ∀ i, p (e i) ↔ i.val < a := by
  classical
  let A := {i : Fin n // p i}
  let B := {i : Fin n // ¬ p i}
  let a := Fintype.card A
  let b := Fintype.card B
  let eA := (Fintype.equivFin A).symm
  let eB := (Fintype.equivFin B).symm
  let e := finSumFinEquiv.symm.trans ((Equiv.sumCongr eA eB).trans (Equiv.sumCompl p))
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hn
  letI : Nonempty A := ⟨⟨i, hi⟩⟩
  letI : Nonempty B := ⟨⟨j, hj⟩⟩
  refine ⟨a, b, Fintype.card_pos, Fintype.card_pos, e, fun k => ?_⟩
  refine Fin.addCases (fun r => ?_) (fun s => ?_) k
  · have h : e (Fin.castAdd b r) = (eA r).val :=
      congrArg (fun v : Fin a ⊕ Fin b => Equiv.sumCompl p (Equiv.sumCongr eA eB v))
        (finSumFinEquiv_symm_apply_castAdd (n := b) r)
    rw [h]
    exact iff_of_true (eA r).property r.isLt
  · have h : e (Fin.natAdd a s) = (eB s).val :=
      congrArg (fun v : Fin a ⊕ Fin b => Equiv.sumCompl p (Equiv.sumCongr eA eB v))
        (finSumFinEquiv_symm_apply_natAdd (m := a) s)
    rw [h]
    exact iff_of_false (eB s).property (not_lt_of_ge (Nat.le_add_right a s.val))

/-- A standard radical element has the same entries as the identity outside the upper-right block. -/
theorem radical_apply_eq_one_of_not_cross
    (u : (twoBlockLevi (g := g) (a := a) (b := b)).ker) (i j : Fin (a + b))
    (h : ¬ (i.val < a ∧ a ≤ j.val)) :
    u.val.val.val i j = (1 : Mt g (a + b)) i j := by
  obtain ⟨X, rfl⟩ := (twoBlockRadicalEquiv (g := g) (a := a) (b := b)).surjective u
  change upperBlockMatrix (1 : Mt g a) X.toAdd (1 : Mt g b) i j = (1 : Mt g (a + b)) i j
  rw [← upperBlockMatrix_one (g := g) (a := a) (b := b)]
  revert h
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · intro _
    simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  · intro h
    exact (h ⟨i.isLt, Nat.le_add_right a j.val⟩).elim
  · intro _
    simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd]
    rfl
  · intro _
    simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]
    rfl

/-- The support of a reindexed radical is contained in the crossing of the chosen split. -/
theorem reindexedRadical_apply_eq_one_of_not_cross {p : Fin n → Prop}
    (e : Fin (a + b) ≃ Fin n) (he : ∀ k, p (e k) ↔ k.val < a)
    (u : (twoBlockLevi (g := g) (a := a) (b := b)).ker) (i j : Fin n)
    (h : ¬ (p i ∧ ¬ p j)) :
    (reindexUnit e u.val.val).val i j = (1 : Mt g n) i j := by
  have h' : ¬ ((e.symm i).val < a ∧ a ≤ (e.symm j).val) := by
    rintro ⟨hi, hj⟩
    apply h
    have hpi := (he (e.symm i)).mpr hi
    have hpj : ¬ p (e (e.symm j)) := fun hpj => (not_lt_of_ge hj) ((he (e.symm j)).mp hpj)
    simpa only [e.apply_symm_apply] using And.intro hpi hpj
  calc
    _ = (1 : Mt g (a + b)) (e.symm i) (e.symm j) :=
      radical_apply_eq_one_of_not_cross u (e.symm i) (e.symm j) h'
    _ = (reindexUnit e (1 : Gn g (a + b))).val i j := rfl
    _ = _ := by rw [map_one]; rfl

end GlobalTheory.GLq
