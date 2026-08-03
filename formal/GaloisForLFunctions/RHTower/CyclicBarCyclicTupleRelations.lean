import GaloisForLFunctions.RHTower.CyclicBarPresentedSimplicial

/-!
# Connes cyclic identities on bar tuples

Right rotation has full order in every degree and intertwines the bar faces and degeneracies by
Connes' four cyclic identities.  These are literal equalities of finite tuples; no homology,
normalization, or degree truncation is used.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {A : Type*}

/-- The basic rotation of `Fin (n+1)` has order dividing `n+1`. -/
theorem finRotate_pow_card (n : ℕ) :
    finRotate (n + 1) ^ (n + 1) = 1 := by
  cases n with
  | zero => rw [finRotate_one]; rfl
  | succ n =>
      apply Equiv.ext
      intro i
      have hmem : i ∈ (finRotate (n + 2)).support := by
        rw [support_finRotate]
        simp
      have hcy : (finRotate (n + 2)).IsCycleOn
          (↑(finRotate (n + 2)).support : Set (Fin (n + 2))) := by
        rw [show (↑(finRotate (n + 2)).support : Set (Fin (n + 2))) =
            {x | finRotate (n + 2) x ≠ x} by
          ext x
          change x ∈ (finRotate (n + 2)).support ↔ finRotate (n + 2) x ≠ x
          exact Equiv.Perm.mem_support]
        exact (isCycle_finRotate (n := n)).isCycleOn
      have h := hcy.pow_card_apply hmem
      simpa [support_finRotate] using h

/-- Rotation sends coordinate zero to the former final coordinate. -/
@[simp]
theorem cyclicBarRotateTuple_zero {n : ℕ} (x : Fin (n + 1) → A) :
    cyclicBarRotateTuple x 0 = x (Fin.last n) := by
  rw [cyclicBarRotateTuple]
  congr 1

/-- Rotation sends each positive coordinate to its predecessor. -/
@[simp]
theorem cyclicBarRotateTuple_succ {n : ℕ} (x : Fin (n + 1) → A) (k : Fin n) :
    cyclicBarRotateTuple x k.succ = x k.castSucc := by
  rw [cyclicBarRotateTuple]
  congr 1
  apply (finRotate (n + 1)).symm_apply_eq.mpr
  exact (finRotate_of_lt (n := n) k.isLt).symm

@[simp]
theorem cyclicBarRotateTuple_one {n : ℕ} (x : Fin (n + 2) → A) :
    cyclicBarRotateTuple x (1 : Fin (n + 2)) = x 0 := by
  change cyclicBarRotateTuple x (0 : Fin (n + 1)).succ =
    x (0 : Fin (n + 1)).castSucc
  exact cyclicBarRotateTuple_succ x 0

/-- Tuple rotation has order `n+1`. -/
theorem cyclicBarRotateTuple_order {n : ℕ} (x : Fin (n + 1) → A) :
    ((cyclicBarRotateTuple : (Fin (n + 1) → A) → (Fin (n + 1) → A))^[n + 1]) x = x := by
  have hiterate : ∀ (m : ℕ) (y : Fin (n + 1) → A),
      ((cyclicBarRotateTuple : (Fin (n + 1) → A) → (Fin (n + 1) → A))^[m]) y =
        fun i => y (((finRotate (n + 1)).symm : Fin (n + 1) → Fin (n + 1))^[m] i) := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
        intro y
        rw [Function.iterate_succ_apply, ih]
        funext i
        change y ((finRotate (n + 1)).symm
          (((finRotate (n + 1)).symm : Fin (n + 1) → Fin (n + 1))^[m] i)) = _
        exact congrArg y
          (Function.iterate_succ_apply'
            ((finRotate (n + 1)).symm : Fin (n + 1) → Fin (n + 1)) m i).symm
  rw [hiterate (n + 1) x]
  funext i
  have hp : (finRotate (n + 1)).symm ^ (n + 1) = 1 := by
    change (finRotate (n + 1))⁻¹ ^ (n + 1) = 1
    rw [inv_pow, finRotate_pow_card, inv_one]
  have hi := DFunLike.congr_fun hp i
  exact congrArg x (by
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq] using hi)

variable [Ring A]

/-- The zero face after rotation is the wrap face. -/
theorem cyclicBarFaceTuple_rotate_zero {n : ℕ} (x : Fin (n + 2) → A) :
    cyclicBarFaceTuple (0 : Fin (n + 2)) (cyclicBarRotateTuple x) =
      cyclicBarFaceTuple (Fin.last (n + 1)) x := by
  rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl]
  simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc, Fin.lastCases_last]
  funext k
  cases k using Fin.cases <;>
    simp [cyclicBarFaceNonwrapTuple, cyclicBarFaceWrapTuple, Fin.init,
      Fin.removeNth, Fin.castSucc_succ]

/-- Every positive face commutes past rotation with the standard index shift. -/
theorem cyclicBarFaceTuple_rotate_succ {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → A) :
    cyclicBarFaceTuple i.succ (cyclicBarRotateTuple x) =
      cyclicBarRotateTuple (cyclicBarFaceTuple i.castSucc x) := by
  induction i using Fin.lastCases with
  | last =>
      have hsucc : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
      rw [hsucc]
      simp only [cyclicBarFaceTuple, Fin.lastCases_last, Fin.lastCases_castSucc]
      funext k
      cases k using Fin.cases with
      | zero =>
          rw [cyclicBarFaceWrapTuple_zero, cyclicBarRotateTuple_zero,
            cyclicBarRotateTuple_zero]
          rw [← hsucc, cyclicBarRotateTuple_succ]
          simp [cyclicBarFaceNonwrapTuple]
      | succ k =>
          rw [cyclicBarFaceWrapTuple_succ, Fin.castSucc_succ,
            cyclicBarRotateTuple_succ, cyclicBarRotateTuple_succ]
          simp [cyclicBarFaceNonwrapTuple, Fin.init]
  | cast i =>
      have hsucc : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      rw [hsucc]
      simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
      rw [cyclicBarFaceNonwrapTuple_eq_contract,
        cyclicBarFaceNonwrapTuple_eq_contract]
      funext k
      cases k using Fin.cases with
      | zero =>
          rw [Fin.contractNth_apply_of_lt _ _ _ _ (Fin.succ_pos _)]
          change cyclicBarRotateTuple x 0 = _
          rw [cyclicBarRotateTuple_zero, cyclicBarRotateTuple_zero]
          rw [Fin.contractNth_apply_of_gt _ _ _ _
            (Fin.castSucc_lt_last i)]
          congr 1
      | succ k =>
          rcases lt_trichotomy k.val i.val with hki | hki | hki
          · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
            rw [Fin.castSucc_succ, cyclicBarRotateTuple_succ,
              cyclicBarRotateTuple_succ]
            rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
          · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)]
            rw [Fin.castSucc_succ, cyclicBarRotateTuple_succ,
              cyclicBarRotateTuple_succ, cyclicBarRotateTuple_succ]
            rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega)]
            simp only [Fin.castSucc_succ]
          · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
            rw [cyclicBarRotateTuple_succ, cyclicBarRotateTuple_succ]
            rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
            simp only [Fin.castSucc_succ]

/-- Every positive degeneracy commutes past rotation with the standard index shift. -/
theorem cyclicBarDegeneracyTuple_rotate_succ {n : ℕ} (i : Fin n)
    (x : Fin (n + 1) → A) :
    cyclicBarDegeneracyTuple i.succ (cyclicBarRotateTuple x) =
      cyclicBarRotateTuple (cyclicBarDegeneracyTuple i.castSucc x) := by
  funext k
  cases k using Fin.cases with
  | zero =>
      rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl]
      rw [cyclicBarDegeneracyTuple_apply_le i.succ 0 (Fin.zero_le _)]
      rw [cyclicBarRotateTuple_zero]
      change x (Fin.last n) = cyclicBarRotateTuple
        (cyclicBarDegeneracyTuple i.castSucc x) 0
      rw [cyclicBarRotateTuple_zero]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
      rw [← hlast]
      rw [cyclicBarDegeneracyTuple_apply_gt i.castSucc (Fin.last n)
        (Fin.castSucc_lt_last i) x]
  | succ k =>
      rw [cyclicBarRotateTuple_succ]
      rcases lt_trichotomy k.val i.succ.val with hki | hki | hki
      · have hkle : k ≤ i.castSucc := by
          change k.val ≤ i.val
          simp only [Fin.val_succ] at hki
          omega
        let l : Fin n := ⟨k.val, lt_of_le_of_lt hkle i.isLt⟩
        have hlk : l.castSucc = k := by ext; rfl
        have hcoord : l.succ.castSucc = k.succ := by ext; rfl
        rw [← hcoord]
        rw [cyclicBarDegeneracyTuple_apply_le i.succ l.succ
          (Fin.succ_le_succ_iff.mpr (by
            change l.val ≤ i.val
            change k.val ≤ i.val at hkle
            exact hkle))]
        rw [cyclicBarRotateTuple_succ, hlk]
        exact (cyclicBarDegeneracyTuple_apply_le i.castSucc k hkle x).symm
      · have hk : k = i.succ := Fin.ext hki
        subst k
        rw [cyclicBarDegeneracyTuple_apply_inserted]
        rw [Fin.castSucc_succ]
        rw [cyclicBarDegeneracyTuple_apply_inserted]
      · cases k using Fin.cases with
        | zero => simp at hki
        | succ k =>
            rw [cyclicBarDegeneracyTuple_apply_gt i.succ k.succ (by
              change i.val + 1 < k.val + 1
              change i.val + 1 < k.val + 1 at hki
              exact hki)]
            rw [cyclicBarRotateTuple_succ]
            rw [Fin.castSucc_succ]
            rw [cyclicBarDegeneracyTuple_apply_gt i.castSucc k.castSucc (by
              change i.val < k.val
              change i.val + 1 < k.val + 1 at hki
              omega)]

/-- The zero degeneracy after rotation is the twice-rotated last degeneracy. -/
theorem cyclicBarDegeneracyTuple_rotate_zero {n : ℕ} (x : Fin (n + 1) → A) :
    cyclicBarDegeneracyTuple 0 (cyclicBarRotateTuple x) =
      cyclicBarRotateTuple
        (cyclicBarRotateTuple (cyclicBarDegeneracyTuple (Fin.last n) x)) := by
  funext k
  cases k using Fin.cases with
  | zero =>
      simp [cyclicBarDegeneracyTuple, Fin.insertNth, Fin.succAboveCases]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
      rw [← hlast, cyclicBarRotateTuple_succ]
      simp
  | succ k =>
      cases k using Fin.cases with
      | zero =>
          simp [cyclicBarDegeneracyTuple, Fin.insertNth, Fin.succAboveCases]
      | succ k =>
          have hne : (k.succ.succ : Fin (n + 2)) ≠ 1 := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
          simp [cyclicBarDegeneracyTuple, Fin.insertNth, Fin.succAboveCases,
            Fin.castSucc_succ, hne]

end RHTower
end GaloisForLFunctions
