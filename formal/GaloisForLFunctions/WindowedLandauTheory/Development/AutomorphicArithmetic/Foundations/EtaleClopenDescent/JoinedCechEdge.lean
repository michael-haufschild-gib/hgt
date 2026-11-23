import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedWeightedCech

/-! The differential of a cocycle extended by zero on the joined cover
is supported on intersections with just one right index. -/

noncomputable section

open GlobalTheory.CechDR GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.WH

variable {k ι κ M : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup M] [Module k M]

@[simp] theorem card_uni (I : Finset ι) (J : Finset κ) : (uni I J).card = I.card + J.card := by
  simp [uni]

@[simp] theorem uni_empty_empty : uni (∅ : Finset ι) (∅ : Finset κ) = ∅ := by
  simp [uni]

/-- Extend cochains by zero outside the left subcover. -/
def extendLeft (a : Finset ι → M) (s : Finset (ι ⊕ₗ κ)) : M :=
  if rgt s = ∅ then a (lft s) else 0

/-- Repeat a cochain on intersections containing exactly one right index. -/
def edge1 (a : Finset ι → M) (s : Finset (ι ⊕ₗ κ)) : M :=
  if (rgt s).card = 1 then a (lft s) else 0

theorem deltaL_uni (a : Finset (ι ⊕ₗ κ) → M) (I : Finset ι) (J : Finset κ) :
    deltaL k (ι ⊕ₗ κ) M a (uni I J) =
      deltaL k ι M (fun S => a (uni S J)) I +
        (-1 : ℤ) ^ I.card • deltaL k κ M (fun S => a (uni I S)) J := by
  have e := wd_uni (1 : (ι ⊕ₗ κ) → Module.End k M) a I J
  change wd (1 : (ι ⊕ₗ κ) → Module.End k M) a (uni I J) =
    wd (1 : ι → Module.End k M) (fun S => a (uni S J)) I +
      (-1 : ℤ) ^ I.card • wd (1 : κ → Module.End k M) (fun S => a (uni I S)) J at e
  simpa only [wd_one] using e

private theorem deltaL_empty_support (y : M) (J : Finset κ) :
    deltaL k κ M (fun S => if S = ∅ then y else 0) J = if J.card = 1 then y else 0 := by
  by_cases hJ : J.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
    simp [deltaL_apply, cubeSign, cechSign, belowCard, Finset.filter_singleton]
  · rw [deltaL_apply, if_neg hJ]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne : J.erase j ≠ ∅ := fun he => hJ (by
      simpa only [he, Finset.card_empty, zero_add] using (Finset.card_erase_add_one hj).symm)
    rw [if_neg hne, smul_zero]

/-- The differential of a left extension is the signed edge of the
left cocycle. -/
theorem deltaL_extendLeft (a : Finset ι → M) (ha : deltaL k ι M a = 0) :
    deltaL k (ι ⊕ₗ κ) M (extendLeft a) =
      fun s => (-1 : ℤ) ^ (lft s).card • edge1 a s := by
  funext s
  obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  rw [deltaL_uni]
  simp only [extendLeft, edge1, lft_uni, rgt_uni, deltaL_empty_support]
  have hz : deltaL k ι M (fun S => if J = ∅ then a S else 0) I = 0 := by
    by_cases he : J = ∅
    · simp only [if_pos he]
      exact congrFun ha I
    · simp only [if_neg he, ← Pi.zero_def, map_zero, Pi.zero_apply]
  rw [hz, zero_add]

end GlobalTheory.WH
