import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

/-!
# A permutation of finite support has a multiplicative sign

On an arbitrary type, a permutation that moves finitely many points restricts to every finite
set that contains its moved points, and the sign of the restriction does not depend on the set.

* `finSign σ`: this sign; `1` when `σ` moves infinitely many points.
* `finSign_mul`: `finSign (σ τ) = finSign σ · finSign τ` for permutations of finite support.
* `finSign_swap`: a transposition has sign `−1`.

Proof. Two finite sets that contain the moved points give restrictions with the same moved
points, and the sign depends only on the action on the moved points. For a product restrict
both factors to the union of their supports.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {α : Type*}

/-- A permutation preserves every set that contains its moved points. -/
theorem apply_mem_iff_of_moved_mem {σ : Perm α} {S : Finset α} (hS : ∀ x, σ x ≠ x → x ∈ S)
    (x : α) : σ x ∈ S ↔ x ∈ S := by
  by_cases h : σ x = x
  · rw [h]
  · exact ⟨fun _ => hS x h, fun _ => hS (σ x) fun h' => h (σ.injective h')⟩

/-- The sign of `σ` on a finite set that contains its moved points. -/
noncomputable def signOn (σ : Perm α) (S : Finset α) (hS : ∀ x, σ x ≠ x → x ∈ S) : ℤˣ :=
  @Perm.sign {x // x ∈ S} (Classical.decEq _) inferInstance
    (σ.subtypePerm (apply_mem_iff_of_moved_mem hS))

/-- The sign on a finite set that contains the moved points does not depend on the set. -/
theorem signOn_eq {σ : Perm α} {S S' : Finset α} (hS : ∀ x, σ x ≠ x → x ∈ S)
    (hS' : ∀ x, σ x ≠ x → x ∈ S') : signOn σ S hS = signOn σ S' hS' := by
  unfold signOn
  exact @Perm.sign_bij {x // x ∈ S} (Classical.decEq _) {x // x ∈ S'} inferInstance
    (Classical.decEq _) inferInstance (σ.subtypePerm (apply_mem_iff_of_moved_mem hS))
    (σ.subtypePerm (apply_mem_iff_of_moved_mem hS'))
    (fun x hx => ⟨x.1, hS' x.1 fun h => hx (Subtype.ext h)⟩)
    (fun x hx hx' => Subtype.ext rfl)
    (fun x₁ x₂ hx₁ hx₂ h => Subtype.ext (congrArg (fun z : {x // x ∈ S'} => z.1) h))
    (fun y hy => ⟨⟨y.1, hS y.1 fun h => hy (Subtype.ext h)⟩,
      fun h => hy (Subtype.ext (congrArg (fun z : {x // x ∈ S} => z.1) h)), Subtype.ext rfl⟩)

open Classical in
/-- **The sign of a permutation of finite support**; `1` if the support is infinite. -/
noncomputable def finSign (σ : Perm α) : ℤˣ :=
  if h : {x | σ x ≠ x}.Finite then signOn σ h.toFinset (fun _ hx => h.mem_toFinset.mpr hx)
  else 1

theorem finSign_eq_signOn (σ : Perm α) {S : Finset α} (hS : ∀ x, σ x ≠ x → x ∈ S) :
    finSign σ = signOn σ S hS := by
  have hfin : {x | σ x ≠ x}.Finite :=
    S.finite_toSet.subset fun x hx => Finset.mem_coe.mpr (hS x hx)
  unfold finSign
  rw [dif_pos hfin]
  exact signOn_eq _ _

/-- **The sign is multiplicative** on the permutations of finite support. -/
theorem finSign_mul {σ τ : Perm α} (hσ : {x | σ x ≠ x}.Finite) (hτ : {x | τ x ≠ x}.Finite) :
    finSign (σ * τ) = finSign σ * finSign τ := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset α, S = hσ.toFinset ∪ hτ.toFinset := ⟨_, rfl⟩
  have hS1 : ∀ x, σ x ≠ x → x ∈ S := fun x hx => by
    rw [hS]
    exact Finset.mem_union_left _ (hσ.mem_toFinset.mpr hx)
  have hS2 : ∀ x, τ x ≠ x → x ∈ S := fun x hx => by
    rw [hS]
    exact Finset.mem_union_right _ (hτ.mem_toFinset.mpr hx)
  have hS3 : ∀ x, (σ * τ) x ≠ x → x ∈ S := fun x hx => by
    by_contra hn
    have h1 : τ x = x := by
      by_contra h
      exact hn (hS2 x h)
    have h2 : σ x = x := by
      by_contra h
      exact hn (hS1 x h)
    exact hx (by rw [Perm.mul_apply, h1, h2])
  rw [finSign_eq_signOn _ hS3, finSign_eq_signOn _ hS1, finSign_eq_signOn _ hS2]
  unfold signOn
  rw [← @Perm.sign_mul _ (Classical.decEq _) inferInstance, Perm.subtypePerm_mul]

/-! ## The permutations of finite support form a group -/

theorem finite_setOf_one_ne : {x | (1 : Perm α) x ≠ x}.Finite := by
  have h : {x | (1 : Perm α) x ≠ x} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    rfl
  rw [h]
  exact Set.finite_empty

theorem finite_setOf_mul_ne {σ τ : Perm α} (hσ : {x | σ x ≠ x}.Finite)
    (hτ : {x | τ x ≠ x}.Finite) : {x | (σ * τ) x ≠ x}.Finite :=
  (hσ.union hτ).subset fun x hx => by
    by_contra h
    rw [Set.mem_union, not_or] at h
    exact hx (by rw [Perm.mul_apply, not_not.mp h.2, not_not.mp h.1])

theorem finite_setOf_inv_ne {σ : Perm α} (hσ : {x | σ x ≠ x}.Finite) :
    {x | σ⁻¹ x ≠ x}.Finite := by
  refine hσ.subset fun x hx h => hx ?_
  show σ⁻¹ x = x
  rw [Perm.inv_eq_iff_eq]
  exact h.symm

/-! ## The values of the sign -/

theorem finSign_one : finSign (1 : Perm α) = 1 := by
  have h := finSign_mul (finite_setOf_one_ne (α := α)) finite_setOf_one_ne
  rw [mul_one] at h
  have h2 := Int.units_mul_self (finSign (1 : Perm α))
  rw [← h] at h2
  exact h2

/-- The inverse of a permutation of finite support has the same sign. -/
theorem finSign_inv {σ : Perm α} (hσ : {x | σ x ≠ x}.Finite) : finSign σ⁻¹ = finSign σ := by
  have hinv := finite_setOf_inv_ne hσ
  have h := finSign_mul hσ hinv
  rw [mul_inv_cancel, finSign_one] at h
  exact mul_left_cancel (h.symm.trans (Int.units_mul_self (finSign σ)).symm)

/-- **A transposition has sign `−1`.** -/
theorem finSign_swap [DecidableEq α] {x y : α} (h : x ≠ y) : finSign (swap x y) = -1 := by
  obtain ⟨S, hSdef⟩ : ∃ S : Finset α, S = {x, y} := ⟨_, rfl⟩
  have hx : x ∈ S := by
    rw [hSdef]
    exact Finset.mem_insert_self _ _
  have hy : y ∈ S := by
    rw [hSdef]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hS : ∀ z, swap x y z ≠ z → z ∈ S := fun z hz => by
    by_contra hn
    exact hz (swap_apply_of_ne_of_ne (fun e => hn (e ▸ hx)) (fun e => hn (e ▸ hy)))
  rw [finSign_eq_signOn _ hS]
  unfold signOn
  have e : (swap x y).subtypePerm (apply_mem_iff_of_moved_mem hS) =
      @swap {z // z ∈ S} (Classical.decEq _) ⟨x, hx⟩ ⟨y, hy⟩ := by
    refine Perm.ext fun z => Subtype.ext ?_
    by_cases hzx : (z : α) = x
    · have hz : z = ⟨x, hx⟩ := Subtype.ext hzx
      rw [hz, @swap_apply_left _ (Classical.decEq _)]
      show swap x y x = y
      exact swap_apply_left x y
    by_cases hzy : (z : α) = y
    · have hz : z = ⟨y, hy⟩ := Subtype.ext hzy
      rw [hz, @swap_apply_right _ (Classical.decEq _)]
      show swap x y y = x
      exact swap_apply_right x y
    · rw [@swap_apply_of_ne_of_ne _ (Classical.decEq _) ⟨x, hx⟩ ⟨y, hy⟩ z
        (fun e => hzx (congrArg Subtype.val e)) (fun e => hzy (congrArg Subtype.val e))]
      show swap x y (z : α) = (z : α)
      exact swap_apply_of_ne_of_ne hzx hzy
  rw [e]
  exact @Perm.sign_swap _ (Classical.decEq _) inferInstance _ _
    fun e' => h (congrArg Subtype.val e')

end GaloisForLFunctions.GaloisTheoryOfZeros
