import GaloisForLFunctions.RHTower.CyclicBarTupleRelations

/-!
# Simplicial identities for cyclic-bar tuple operators

This file proves every generator relation in the simplex-category presentation before passing to
tensor products.  Generic insertion/contraction lemmas isolate the finite-index bookkeeping; the
bar identities then use only associativity and the two unit laws of the coefficient ring.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {A : Type*} [Ring A]

/-- Before the inserted unit, degeneracy preserves tuple entries. -/
theorem cyclicBarDegeneracyTuple_apply_le {n : ℕ} (i k : Fin (n + 1)) (hki : k ≤ i)
    (x : Fin (n + 1) → A) :
    cyclicBarDegeneracyTuple i x k.castSucc = x k := by
  rw [cyclicBarDegeneracyTuple,
    ← Fin.succAbove_of_castSucc_lt i.succ k
      (Fin.castSucc_lt_succ_iff.mpr hki)]
  exact Fin.insertNth_apply_succAbove _ _ _ _

/-- After the inserted unit, degeneracy shifts tuple entries once. -/
theorem cyclicBarDegeneracyTuple_apply_gt {n : ℕ} (i k : Fin (n + 1)) (hik : i < k)
    (x : Fin (n + 1) → A) :
    cyclicBarDegeneracyTuple i x k.succ = x k := by
  rw [cyclicBarDegeneracyTuple,
    ← Fin.succAbove_of_le_castSucc i.succ k (Fin.succ_le_castSucc_iff.mpr hik)]
  exact Fin.insertNth_apply_succAbove _ _ _ _

/-- Degeneracy has value one at its inserted coordinate. -/
@[simp]
theorem cyclicBarDegeneracyTuple_apply_inserted {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → A) :
    cyclicBarDegeneracyTuple i x i.succ = 1 := by
  exact Fin.insertNth_apply_same _ _ _

/-- Contracting strictly before an insertion commutes with that insertion, with its index shifted
down after contraction. -/
theorem cyclicBar_contract_insert_before {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j)
    (x : Fin (n + 2) → A) :
    Fin.contractNth i.castSucc.castSucc (fun a b : A => a * b)
        (cyclicBarDegeneracyTuple j.succ x) =
      cyclicBarDegeneracyTuple j
        (Fin.contractNth i.castSucc (fun a b : A => a * b) x) := by
  funext k
  cases k using j.succ.succAboveCases with
  | x =>
      rw [cyclicBarDegeneracyTuple_apply_inserted]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by
        change i.val < j.val + 1
        omega)]
      rw [cyclicBarDegeneracyTuple_apply_inserted]
  | p k =>
      change _ = Fin.insertNth (α := fun _ => A) j.succ 1
        (Fin.contractNth i.castSucc (fun a b : A => a * b) x)
          (j.succ.succAbove k)
      rw [Fin.insertNth_apply_succAbove]
      rcases lt_trichotomy k.val i.val with hki | hki | hki
      · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by
          change (j.succ.succAbove k).val < i.val
          rw [Fin.succAbove_of_castSucc_lt]
          · exact hki
          · change k.val < j.val + 1
            omega)]
        rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
        rw [Fin.succAbove_of_castSucc_lt _ _ (by
          change k.val < j.val + 1
          omega)]
        exact cyclicBarDegeneracyTuple_apply_le j.succ k.castSucc (by
          change k.val ≤ j.val + 1
          omega) x
      · have hk : k = i := Fin.ext hki
        subst k
        rw [Fin.succAbove_of_castSucc_lt _ _ (by
          change i.val < j.val + 1
          omega)]
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
        rw [cyclicBarDegeneracyTuple_apply_le j.succ i.castSucc (by
          change i.val ≤ j.val + 1
          omega) x]
        rw [← Fin.castSucc_succ]
        rw [cyclicBarDegeneracyTuple_apply_le j.succ i.succ
          (Fin.succ_le_succ_iff.mpr hij) x]
      · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by
          change i.val < (j.succ.succAbove k).val
          by_cases hkj : k ≤ j
          · rw [Fin.succAbove_of_castSucc_lt _ _ (by
              change k.val < j.val + 1
              omega)]
            exact hki
          · rw [Fin.succAbove_of_le_castSucc _ _ (by
              change j.val + 1 ≤ k.val
              omega)]
            simp only [Fin.val_succ]
            omega)]
        rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
        by_cases hkj : k ≤ j
        · rw [Fin.succAbove_of_castSucc_lt _ _ (by
            change k.val < j.val + 1
            omega)]
          rw [← Fin.castSucc_succ]
          exact cyclicBarDegeneracyTuple_apply_le j.succ k.succ
            (Fin.succ_le_succ_iff.mpr hkj) x
        · rw [Fin.succAbove_of_le_castSucc _ _ (by
            change j.val + 1 ≤ k.val
            omega)]
          exact cyclicBarDegeneracyTuple_apply_gt j.succ k.succ (by
            change j.val + 1 < k.val + 1
            omega) x

/-- Contracting strictly after an insertion commutes with that insertion, with the contraction
index shifted down. -/
theorem cyclicBar_contract_insert_after {n : ℕ} (i j : Fin (n + 1)) (hji : j < i)
    (x : Fin (n + 2) → A) :
    Fin.contractNth i.succ.castSucc (fun a b : A => a * b)
        (cyclicBarDegeneracyTuple j.castSucc x) =
      cyclicBarDegeneracyTuple j
        (Fin.contractNth i.castSucc (fun a b : A => a * b) x) := by
  funext k
  cases k using j.succ.succAboveCases with
  | x =>
      rw [cyclicBarDegeneracyTuple_apply_inserted]
      rw [Fin.contractNth_apply_of_lt _ _ _ _ (by
        change j.val + 1 < i.val + 1
        omega)]
      rw [Fin.castSucc_succ]
      rw [cyclicBarDegeneracyTuple_apply_inserted]
  | p k =>
      change _ = Fin.insertNth (α := fun _ => A) j.succ 1
        (Fin.contractNth i.castSucc (fun a b : A => a * b) x)
          (j.succ.succAbove k)
      rw [Fin.insertNth_apply_succAbove]
      rcases lt_trichotomy k.val i.val with hki | hki | hki
      · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by
          change (j.succ.succAbove k).val < i.val + 1
          by_cases hkj : k ≤ j
          · rw [Fin.succAbove_of_castSucc_lt _ _ (by
              change k.val < j.val + 1
              omega)]
            exact Nat.lt_succ_of_lt hki
          · rw [Fin.succAbove_of_le_castSucc _ _ (by
              change j.val + 1 ≤ k.val
              omega)]
            simp only [Fin.val_succ]
            omega)]
        rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
        by_cases hkj : k ≤ j
        · rw [Fin.succAbove_of_castSucc_lt _ _ (by
            change k.val < j.val + 1
            omega)]
          exact cyclicBarDegeneracyTuple_apply_le j.castSucc k.castSucc (by
            change k.val ≤ j.val
            exact hkj) x
        · rw [Fin.succAbove_of_le_castSucc _ _ (by
            change j.val + 1 ≤ k.val
            omega)]
          rw [Fin.castSucc_succ]
          exact cyclicBarDegeneracyTuple_apply_gt j.castSucc k.castSucc (by
            change j.val < k.val
            omega) x
      · have hk : k = i := Fin.ext hki
        subst k
        rw [Fin.succAbove_of_le_castSucc _ _ (by
          change j.val + 1 ≤ i.val
          omega)]
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
        rw [Fin.castSucc_succ]
        rw [cyclicBarDegeneracyTuple_apply_gt j.castSucc i.castSucc (by
          change j.val < i.val
          omega) x]
        rw [cyclicBarDegeneracyTuple_apply_gt j.castSucc i.succ (by
          change j.val < i.val + 1
          omega) x]
      · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by
          change i.val + 1 < (j.succ.succAbove k).val
          rw [Fin.succAbove_of_le_castSucc _ _ (by
            change j.val + 1 ≤ k.val
            omega)]
          simp only [Fin.val_succ]
          omega)]
        rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
        rw [Fin.succAbove_of_le_castSucc _ _ (by
          change j.val + 1 ≤ k.val
          omega)]
        exact cyclicBarDegeneracyTuple_apply_gt j.castSucc k.succ (by
          change j.val < k.val + 1
          omega) x

/-- Wrap contraction commutes with every unit insertion that occurs after coordinate zero. -/
theorem cyclicBar_wrap_insert {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 2) → A) :
    cyclicBarFaceWrapTuple (cyclicBarDegeneracyTuple j.castSucc x) =
      cyclicBarDegeneracyTuple j (cyclicBarFaceWrapTuple x) := by
  funext k
  cases k using j.succ.succAboveCases with
  | x =>
      rw [cyclicBarDegeneracyTuple_apply_inserted]
      rw [cyclicBarFaceWrapTuple_succ]
      rw [Fin.castSucc_succ]
      exact cyclicBarDegeneracyTuple_apply_inserted j.castSucc x
  | p k =>
      change cyclicBarFaceWrapTuple (cyclicBarDegeneracyTuple j.castSucc x)
          (j.succ.succAbove k) =
        Fin.insertNth (α := fun _ => A) j.succ 1 (cyclicBarFaceWrapTuple x)
          (j.succ.succAbove k)
      rw [Fin.insertNth_apply_succAbove]
      cases k using Fin.cases with
      | zero =>
          rw [Fin.succAbove_of_castSucc_lt _ _ (by
            change 0 < j.val + 1
            omega)]
          change cyclicBarFaceWrapTuple (cyclicBarDegeneracyTuple j.castSucc x) 0 =
            cyclicBarFaceWrapTuple x 0
          rw [cyclicBarFaceWrapTuple_zero, cyclicBarFaceWrapTuple_zero]
          have hlast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by ext; simp
          rw [← hlast]
          rw [cyclicBarDegeneracyTuple_apply_gt j.castSucc (Fin.last (n + 1))
            (Fin.castSucc_lt_last j) x]
          rw [show (0 : Fin (n + 3)) = (0 : Fin (n + 2)).castSucc by rfl]
          rw [cyclicBarDegeneracyTuple_apply_le j.castSucc 0 (Fin.zero_le _) x]
      | succ k =>
          by_cases hkj : k.succ ≤ j
          · have hkjv : k.val + 1 ≤ j.val := by
              change k.val + 1 ≤ j.val at hkj
              exact hkj
            rw [Fin.succAbove_of_castSucc_lt _ _ (by
              change k.val + 1 < j.val + 1
              omega)]
            rw [Fin.castSucc_succ]
            rw [cyclicBarFaceWrapTuple_succ, cyclicBarFaceWrapTuple_succ]
            exact cyclicBarDegeneracyTuple_apply_le j.castSucc k.succ.castSucc
              (Fin.castSucc_le_castSucc_iff.mpr hkj) x
          · have hkjv : j.val < k.val + 1 := by
              change ¬k.val + 1 ≤ j.val at hkj
              omega
            rw [Fin.succAbove_of_le_castSucc _ _ (by
              change j.val + 1 ≤ k.val + 1
              omega)]
            rw [cyclicBarFaceWrapTuple_succ, cyclicBarFaceWrapTuple_succ]
            rw [Fin.castSucc_succ]
            exact cyclicBarDegeneracyTuple_apply_gt j.castSucc k.succ.castSucc hkjv x

omit [Ring A] in
/-- Two ordered unit insertions commute after the standard index shift. -/
theorem cyclicBar_insert_insert {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j)
    (a b : A) (x : Fin (n + 1) → A) :
    Fin.insertNth (α := fun _ => A) i.castSucc.succ a
        (Fin.insertNth (α := fun _ => A) j.succ b x) =
      Fin.insertNth (α := fun _ => A) j.succ.succ b
        (Fin.insertNth (α := fun _ => A) i.succ a x) := by
  funext k
  cases k using i.castSucc.succ.succAboveCases with
  | x =>
      simp only [Fin.insertNth_apply_same]
      have heq : j.succ.succ.succAbove i.succ = i.castSucc.succ := by
        rw [Fin.succAbove_of_castSucc_lt]
        · exact Fin.castSucc_succ i
        · change i.val + 1 < j.val + 2
          omega
      rw [← heq, Fin.insertNth_apply_succAbove,
        Fin.insertNth_apply_same]
  | p k =>
      simp only [Fin.insertNth_apply_succAbove]
      cases k using j.succ.succAboveCases with
      | x =>
          simp only [Fin.insertNth_apply_same]
          have hp : i.castSucc.succ ≤ j.succ.castSucc := by
            change i.val + 1 ≤ j.val + 1
            omega
          rw [Fin.succAbove_of_le_castSucc _ _ hp]
          rw [Fin.insertNth_apply_same]
      | p k =>
          simp only [Fin.insertNth_apply_succAbove]
          have heq :
              i.castSucc.succ.succAbove (j.succ.succAbove k) =
                j.succ.succ.succAbove (i.succ.succAbove k) := by
            calc
              i.castSucc.succ.succAbove (j.succ.succAbove k) =
                  (i.castSucc.succ.succAbove j.succ).succAbove
                    ((j.succ.predAbove i.castSucc.succ).succAbove k) :=
                (Fin.succAbove_succAbove_succAbove_predAbove
                  i.castSucc.succ j.succ k).symm
              _ = j.succ.succ.succAbove (i.succ.succAbove k) := by
                rw [← Fin.castSucc_succ]
                rw [Fin.succAbove_castSucc_of_le _ _
                  (Fin.succ_le_succ_iff.mpr hij)]
                rw [Fin.predAbove_castSucc_of_le _ _
                  (Fin.succ_le_succ_iff.mpr hij)]
          rw [heq]
          simp

/-- A face cancels the unit inserted immediately after the face's left factor. -/
theorem cyclicBarFaceTuple_degeneracyTuple_self {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → A) :
    cyclicBarFaceTuple i.castSucc (cyclicBarDegeneracyTuple i x) = x := by
  simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
  rw [cyclicBarFaceNonwrapTuple_eq_contract]
  funext k
  rcases lt_trichotomy k.val i.val with hki | hki | hki
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
    exact cyclicBarDegeneracyTuple_apply_le i k (Fin.le_of_lt hki) x
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ hki]
    have hk : k = i := Fin.ext hki
    subst k
    rw [cyclicBarDegeneracyTuple_apply_le i i (Fin.le_refl i),
      cyclicBarDegeneracyTuple_apply_inserted]
    simp
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
    exact cyclicBarDegeneracyTuple_apply_gt i k hki x

/-- A face also cancels the unit when it is the right factor of the contraction. -/
theorem cyclicBarFaceTuple_degeneracyTuple_succ {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → A) :
    cyclicBarFaceTuple i.succ (cyclicBarDegeneracyTuple i x) = x := by
  induction i using Fin.lastCases with
  | last =>
      have hsucc : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
      rw [hsucc]
      simp only [cyclicBarFaceTuple, Fin.lastCases_last]
      funext k
      cases k using Fin.cases <;>
        simp [cyclicBarFaceWrapTuple, cyclicBarDegeneracyTuple]
  | cast i =>
      have hsucc : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      rw [hsucc]
      simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
      rw [cyclicBarFaceNonwrapTuple_eq_contract]
      funext k
      rcases lt_trichotomy k.val i.succ.val with hki | hki | hki
      · rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
        exact cyclicBarDegeneracyTuple_apply_le i.castSucc k (by
          change k.val ≤ i.val
          simp only [Fin.val_succ] at *
          omega) x
      · rw [Fin.contractNth_apply_of_eq _ _ _ _ hki]
        have hk : k = i.succ := Fin.ext hki
        subst k
        rw [Fin.castSucc_succ, cyclicBarDegeneracyTuple_apply_inserted]
        rw [cyclicBarDegeneracyTuple_apply_gt i.castSucc i.succ (by simp) x]
        simp
      · rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
        exact cyclicBarDegeneracyTuple_apply_gt i.castSucc k (by
          change i.val < k.val
          simp only [Fin.val_succ] at *
          omega) x

/-- Face and degeneracy commute in the ordered case before the inserted unit. -/
theorem cyclicBarFaceTuple_degeneracyTuple_of_le {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (x : Fin (n + 2) → A) :
    cyclicBarFaceTuple i.castSucc (cyclicBarDegeneracyTuple j.succ x) =
      cyclicBarDegeneracyTuple j (cyclicBarFaceTuple i x) := by
  induction i using Fin.lastCases with
  | last => exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last j)) hij)
  | cast i =>
      simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
      rw [cyclicBarFaceNonwrapTuple_eq_contract,
        cyclicBarFaceNonwrapTuple_eq_contract]
      exact cyclicBar_contract_insert_before i j
        (Fin.castSucc_le_castSucc_iff.mp hij) x

/-- Face and degeneracy commute in the ordered case after the inserted unit, including the wrap
face. -/
theorem cyclicBarFaceTuple_degeneracyTuple_of_gt {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) (x : Fin (n + 2) → A) :
    cyclicBarFaceTuple i.succ (cyclicBarDegeneracyTuple j.castSucc x) =
      cyclicBarDegeneracyTuple j (cyclicBarFaceTuple i x) := by
  induction i using Fin.lastCases with
  | last =>
      have hsucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by ext; simp
      rw [hsucc]
      simp only [cyclicBarFaceTuple, Fin.lastCases_last]
      exact cyclicBar_wrap_insert j x
  | cast i =>
      have hsucc : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      rw [hsucc]
      simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
      rw [cyclicBarFaceNonwrapTuple_eq_contract,
        cyclicBarFaceNonwrapTuple_eq_contract]
      exact cyclicBar_contract_insert_after i j
        (Fin.castSucc_lt_castSucc_iff.mp hji) x

/-- All cyclic-bar degeneracies satisfy the degeneracy--degeneracy simplicial identity. -/
theorem cyclicBarDegeneracyTuple_degeneracyTuple {n : ℕ} (i j : Fin (n + 1))
    (hij : i ≤ j) (x : Fin (n + 1) → A) :
    cyclicBarDegeneracyTuple i.castSucc (cyclicBarDegeneracyTuple j x) =
      cyclicBarDegeneracyTuple j.succ (cyclicBarDegeneracyTuple i x) := by
  exact cyclicBar_insert_insert i j hij 1 1 x

end RHTower
end GaloisForLFunctions
