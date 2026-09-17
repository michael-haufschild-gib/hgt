import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FieldSimp

/-!
# Pair order under a uniform permutation

Swapping two target labels pairs every permutation in which `e` arrives first with one in which
`f` arrives first. Consequently each event has exactly half of the symmetric group. This is the
finite counting form of the fairness step used after snapshot independence.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

variable {α : Type*} [DecidableEq α] [LinearOrder α]

/-- In the order encoded by `σ`, the position of `e` is earlier than the position of `f`. -/
def ArrivesBefore (e f : α) (σ : Equiv.Perm α) : Prop :=
  σ.symm e < σ.symm f

instance (e f : α) : DecidablePred (ArrivesBefore e f) :=
  fun σ => inferInstanceAs (Decidable (σ.symm e < σ.symm f))

/-- Swap the two target labels of an arrival order. -/
def swapArrivalTargets (e f : α) (σ : Equiv.Perm α) : Equiv.Perm α :=
  σ.trans (Equiv.swap e f)

theorem arrivesBefore_swapArrivalTargets (e f : α) (σ : Equiv.Perm α) :
    ArrivesBefore f e (swapArrivalTargets e f σ) ↔ ArrivesBefore e f σ := by
  simp [ArrivesBefore, swapArrivalTargets]

/-- Target swapping bijects the two possible strict relative orders. -/
def arrivesBeforeSwapEquiv (e f : α) :
    {σ : Equiv.Perm α // ArrivesBefore e f σ} ≃
      {σ : Equiv.Perm α // ArrivesBefore f e σ} where
  toFun σ := ⟨swapArrivalTargets e f σ, (arrivesBefore_swapArrivalTargets e f σ).2 σ.2⟩
  invFun σ := ⟨swapArrivalTargets e f σ, by
    simpa [ArrivesBefore, swapArrivalTargets] using σ.2⟩
  left_inv σ := by
    apply Subtype.ext
    ext x
    simp [swapArrivalTargets]
  right_inv σ := by
    apply Subtype.ext
    ext x
    simp [swapArrivalTargets]

omit [DecidableEq α] in
theorem not_arrivesBefore_iff_reverse {e f : α} (hef : e ≠ f) (σ : Equiv.Perm α) :
    ¬ArrivesBefore e f σ ↔ ArrivesBefore f e σ := by
  unfold ArrivesBefore
  have hpos : σ.symm e ≠ σ.symm f := fun h => hef (σ.symm.injective h)
  constructor
  · intro hnot
    rcases lt_or_gt_of_ne hpos with hlt | hgt
    · exact False.elim (hnot hlt)
    · exact hgt
  · exact fun hrev hforward => asymm hforward hrev

def notArrivesBeforeEquivReverse {e f : α} (hef : e ≠ f) :
    {σ : Equiv.Perm α // ¬ArrivesBefore e f σ} ≃
      {σ : Equiv.Perm α // ArrivesBefore f e σ} :=
  Equiv.subtypeEquiv (Equiv.refl _) (not_arrivesBefore_iff_reverse hef)

/-- Every permutation lies in exactly one of the two strict pair-order events. -/
def permBeforePartitionEquiv {e f : α} (hef : e ≠ f) :
    Equiv.Perm α ≃
      {σ : Equiv.Perm α // ArrivesBefore e f σ} ⊕
        {σ : Equiv.Perm α // ArrivesBefore f e σ} :=
  (Equiv.sumCompl (ArrivesBefore e f)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (notArrivesBeforeEquivReverse hef))

section Finite

variable [Fintype α]

/-- Exactly half of the symmetric group puts `e` before a distinct `f`. -/
theorem two_mul_card_arrivesBefore {e f : α} (hef : e ≠ f) :
    2 * Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} =
      (Fintype.card α).factorial := by
  have hpartition := Fintype.card_congr (permBeforePartitionEquiv hef)
  have hswap := Fintype.card_congr (arrivesBeforeSwapEquiv e f)
  rw [Fintype.card_perm, Fintype.card_sum] at hpartition
  calc
    2 * Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} =
        Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} +
          Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} := two_mul _
    _ = Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} +
          Fintype.card {σ : Equiv.Perm α // ArrivesBefore f e σ} :=
      congrArg _ hswap
    _ = (Fintype.card α).factorial := hpartition.symm

/-- Rational probability mass of the pair-order event under a uniform permutation. -/
theorem uniform_permutation_arrivesBefore_mass {e f : α} (hef : e ≠ f) :
    (Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} : ℚ) /
        ((Fintype.card α).factorial : ℚ) = 1 / 2 := by
  have hfac : (Fintype.card α).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hfacQ : ((Fintype.card α).factorial : ℚ) ≠ 0 := by exact_mod_cast hfac
  field_simp [hfacQ]
  have hQ :
      (2 : ℚ) * (Fintype.card {σ : Equiv.Perm α // ArrivesBefore e f σ} : ℚ) =
        ((Fintype.card α).factorial : ℚ) := by
    exact_mod_cast two_mul_card_arrivesBefore hef
  simpa [mul_comm] using hQ

end Finite

end GaloisForLFunctions.HTGeometry
