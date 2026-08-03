import GaloisForLFunctions.RHTower.CyclicBarTensorOperators

/-!
# Relations among cyclic-bar tuple operators

The central contraction law below isolates the only noncommutative issue in the ordinary face
identities: coincident contractions are exactly associativity; separated contractions commute
without permuting factors.
-/

noncomputable section

open Function

namespace GaloisForLFunctions
namespace RHTower

variable {A : Type*}

section Semigroup

variable [Semigroup A]

/-- Two coincident adjacent contractions agree by associativity. -/
theorem cyclicBar_contract_contract_eq {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 3) → A) :
    Fin.contractNth i (fun a b : A ↦ a * b)
        (Fin.contractNth i.succ (fun a b : A ↦ a * b) x) =
      Fin.contractNth i (fun a b : A ↦ a * b)
        (Fin.contractNth i.castSucc (fun a b : A ↦ a * b) x) := by
  funext k
  rcases lt_trichotomy k.val i.val with hki | hki | hki
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
  · have hkie : k.castSucc = i := by ext; simpa using hki
    rw [Fin.contractNth_apply_of_eq _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_eq _ _ _ _ hki]
    calc
      Fin.contractNth i.succ (fun a b : A ↦ a * b) x k.castSucc *
          Fin.contractNth i.succ (fun a b : A ↦ a * b) x k.succ =
          x k.castSucc.castSucc * (x k.succ.castSucc * x k.succ.succ) := by
            congr 1
            · exact Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)
            · exact Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)
      _ = (x k.castSucc.castSucc * x k.castSucc.succ) * x k.succ.succ := by
            rw [Fin.castSucc_succ]
            exact (mul_assoc (x k.castSucc.castSucc) (x k.castSucc.succ)
              (x k.succ.succ)).symm
      _ = Fin.contractNth i.castSucc (fun a b : A ↦ a * b) x k.castSucc *
          Fin.contractNth i.castSucc (fun a b : A ↦ a * b) x k.succ := by
            congr 1
            · exact (Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)).symm
            · exact (Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)).symm
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
    rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]

/-- Separated adjacent contractions commute. -/
theorem cyclicBar_contract_contract_lt {n : ℕ} (i j : Fin (n + 2)) (hij : i < j)
    (x : Fin (n + 3) → A) :
    Fin.contractNth i (fun a b : A ↦ a * b)
        (Fin.contractNth j.succ (fun a b : A ↦ a * b) x) =
      Fin.contractNth j (fun a b : A ↦ a * b)
        (Fin.contractNth i.castSucc (fun a b : A ↦ a * b) x) := by
  funext k
  rcases lt_trichotomy k.val i.val with hki | hki | hki
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by omega)]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ hki]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by omega)]
    rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)]
    rw [Fin.castSucc_succ]
  · rcases lt_trichotomy k.val j.val with hkj | hkj | hkj
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
      rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
      rw [Fin.contractNth_apply_of_lt _ _ _ _ hkj]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
      rw [Fin.castSucc_succ]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ hkj]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
      rw [Fin.castSucc_succ]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ hki]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ hkj]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]

end Semigroup

variable [Ring A]

/-- The update/remove implementation of a non-wrap face is `Fin.contractNth`. -/
theorem cyclicBarFaceNonwrapTuple_eq_contract {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → A) :
    cyclicBarFaceNonwrapTuple i x =
      Fin.contractNth i.castSucc (fun a b : A ↦ a * b) x := by
  funext k
  rcases lt_trichotomy k.val i.val with hki | hki | hki
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using hki)]
    rw [cyclicBarFaceNonwrapTuple, Function.update_of_ne (Fin.ne_of_lt hki)]
    change x (i.succ.succAbove k) = x k.castSucc
    rw [Fin.succAbove_of_castSucc_lt]
    simpa using hki.le
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using hki)]
    have h : k = i := Fin.ext hki
    subst k
    simp [cyclicBarFaceNonwrapTuple]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using hki)]
    rw [cyclicBarFaceNonwrapTuple, Function.update_of_ne (Fin.ne_of_gt hki)]
    change x (i.succ.succAbove k) = x k.succ
    rw [Fin.succAbove_of_le_castSucc]
    simpa using hki

@[simp]
theorem cyclicBarFaceWrapTuple_zero {n : ℕ} (x : Fin (n + 2) → A) :
    cyclicBarFaceWrapTuple x 0 = x (Fin.last (n + 1)) * x 0 := by
  simp [cyclicBarFaceWrapTuple]

@[simp]
theorem cyclicBarFaceWrapTuple_succ {n : ℕ} (x : Fin (n + 2) → A) (k : Fin n) :
    cyclicBarFaceWrapTuple x k.succ = x k.succ.castSucc := by
  simp [cyclicBarFaceWrapTuple, Fin.init]

@[simp]
theorem cyclicBarFaceWrapTuple_one {n : ℕ} (x : Fin (n + 3) → A) :
    cyclicBarFaceWrapTuple x (1 : Fin (n + 2)) = x 1 := by
  change cyclicBarFaceWrapTuple x (0 : Fin (n + 1)).succ =
    x (0 : Fin (n + 1)).succ.castSucc
  exact cyclicBarFaceWrapTuple_succ x 0

/-- All noncommutative cyclic-bar faces satisfy the face--face simplicial identity.  The cases
meeting the wrap face are precisely the boundary associativity cases. -/
theorem cyclicBarFaceTuple_faceTuple {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j)
    (x : Fin (n + 3) → A) :
    cyclicBarFaceTuple i (cyclicBarFaceTuple j.succ x) =
      cyclicBarFaceTuple j (cyclicBarFaceTuple i.castSucc x) := by
  induction j using Fin.lastCases with
  | cast j =>
      induction i using Fin.lastCases with
      | last =>
          exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last j)) hij)
      | cast i =>
          have hsucc : j.castSucc.succ = j.succ.castSucc := by ext; rfl
          rw [hsucc]
          simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
          rw [cyclicBarFaceNonwrapTuple_eq_contract,
            cyclicBarFaceNonwrapTuple_eq_contract,
            cyclicBarFaceNonwrapTuple_eq_contract,
            cyclicBarFaceNonwrapTuple_eq_contract]
          by_cases h : i = j
          · subst j
            exact cyclicBar_contract_contract_eq i.castSucc x
          · exact cyclicBar_contract_contract_lt i.castSucc j.castSucc
              (Fin.castSucc_lt_castSucc_iff.mpr (lt_of_le_of_ne
                (Fin.castSucc_le_castSucc_iff.mp hij) h)) x
  | last =>
      induction i using Fin.lastCases with
      | last =>
          have hsucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by ext; simp
          rw [hsucc]
          simp only [cyclicBarFaceTuple, Fin.lastCases_last]
          rw [Fin.lastCases_castSucc]
          change cyclicBarFaceWrapTuple (cyclicBarFaceWrapTuple x) =
            cyclicBarFaceWrapTuple (cyclicBarFaceNonwrapTuple (Fin.last (n + 1)) x)
          funext k
          cases k using Fin.cases <;>
            simp [cyclicBarFaceWrapTuple, cyclicBarFaceNonwrapTuple, Fin.init, mul_assoc]
      | cast i =>
          have hsucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by ext; simp
          rw [hsucc]
          simp only [cyclicBarFaceTuple, Fin.lastCases_last, Fin.lastCases_castSucc]
          change cyclicBarFaceNonwrapTuple i (cyclicBarFaceWrapTuple x) =
            cyclicBarFaceWrapTuple (cyclicBarFaceNonwrapTuple i.castSucc x)
          rw [cyclicBarFaceNonwrapTuple_eq_contract,
            cyclicBarFaceNonwrapTuple_eq_contract]
          cases i using Fin.cases with
          | zero =>
              funext k
              cases k using Fin.cases <;>
                simp [Fin.contractNth_apply_of_eq, Fin.contractNth_apply_of_gt, mul_assoc]
          | succ i =>
              funext k
              cases k using Fin.cases with
              | zero =>
                  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by
                    change 0 < i.val + 1
                    omega)]
                  change cyclicBarFaceWrapTuple x 0 = _
                  rw [cyclicBarFaceWrapTuple_zero, cyclicBarFaceWrapTuple_zero]
                  rw [Fin.contractNth_apply_of_gt _ _ _ _
                    (Fin.castSucc_lt_last i.succ)]
                  rw [Fin.contractNth_apply_of_lt _ _ _ _ (Fin.succ_pos i)]
                  rw [hsucc]
                  rfl
              | succ k =>
                  rcases lt_trichotomy k.val i.val with hki | hki | hki
                  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
                    rw [Fin.castSucc_succ, cyclicBarFaceWrapTuple_succ,
                      cyclicBarFaceWrapTuple_succ]
                    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
                    simp only [Fin.castSucc_succ]
                  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)]
                    rw [Fin.castSucc_succ, cyclicBarFaceWrapTuple_succ,
                      cyclicBarFaceWrapTuple_succ, cyclicBarFaceWrapTuple_succ]
                    rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)]
                    simp only [Fin.castSucc_succ]
                  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
                    rw [cyclicBarFaceWrapTuple_succ, cyclicBarFaceWrapTuple_succ]
                    rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
                    simp only [Fin.castSucc_succ]

end RHTower
end GaloisForLFunctions
