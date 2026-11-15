import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm

/-!
# Counting pointed finite labellings

A set of `n+1` elements has `n!` bijections with `Fin (n+1)` sending a chosen
point to zero. Fixing one such bijection reduces the count to permutations
of the remaining `n` labels.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.TransitiveActions

private theorem decomposeFin_fst {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
  calc
    _ = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin σ) 0 :=
      (Equiv.Perm.decomposeFin_symm_apply_zero _ _).symm
    _ = σ 0 := congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e 0)
      (Equiv.Perm.decomposeFin.symm_apply_apply σ)

/-- Fixing the distinguished label leaves an arbitrary permutation of the other labels. -/
def pointedPermEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = 0} ≃ Equiv.Perm (Fin n) where
  toFun σ := (Equiv.Perm.decomposeFin σ.val).2
  invFun τ := ⟨Equiv.Perm.decomposeFin.symm (0, τ), by simp⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.Perm.decomposeFin.injective
    rw [Equiv.Perm.decomposeFin.apply_symm_apply]
    exact Prod.ext (by rw [decomposeFin_fst, σ.property]) rfl
  right_inv τ := by simp

/-- A fixed pointed labelling identifies every other pointed labelling with a fixed-point permutation. -/
def pointedEquivPerm {Q : Type*} {n : ℕ} (q₀ : Q) (e₀ : Q ≃ Fin (n + 1))
    (he₀ : e₀ q₀ = 0) :
    {e : Q ≃ Fin (n + 1) // e q₀ = 0} ≃
      {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = 0} where
  toFun e := ⟨e₀.symm.trans e.val, by
    change e.val (e₀.symm 0) = 0
    have hs : e₀.symm 0 = q₀ := e₀.symm_apply_eq.mpr he₀.symm
    rw [hs, e.property]⟩
  invFun σ := ⟨e₀.trans σ.val, by
    change σ.val (e₀ q₀) = 0
    rw [he₀, σ.property]⟩
  left_inv e := by apply Subtype.ext; ext q; simp
  right_inv σ := by apply Subtype.ext; ext q; simp

/-- A set with `n+1` points has exactly `n!` labellings fixing one point. -/
theorem card_pointedEquiv (Q : Type*) (q₀ : Q) (n : ℕ) (hcard : Nat.card Q = n + 1) :
    Nat.card {e : Q ≃ Fin (n + 1) // e q₀ = 0} = n.factorial := by
  classical
  letI : Finite Q := Nat.finite_of_card_ne_zero (hcard ▸ Nat.succ_ne_zero n)
  letI : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (n + 1) := Fintype.equivFinOfCardEq
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  let e₀ := e.trans (Equiv.swap (e q₀) 0)
  have he₀ : e₀ q₀ = 0 := Equiv.swap_apply_left _ _
  rw [Nat.card_congr (pointedEquivPerm q₀ e₀ he₀), Nat.card_congr (pointedPermEquiv n),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

#print axioms card_pointedEquiv
end GaloisForLFunctions.RepresentationLifting.TransitiveActions
