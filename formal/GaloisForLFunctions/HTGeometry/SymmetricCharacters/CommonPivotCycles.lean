import GaloisForLFunctions.HTGeometry.SymmetricCharacters.ReplicatedKernel
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Cycle moments from permutations with a common pivot

Two cycles sharing only their pivot multiply, after inverting the first, to one cycle on the
combined arms. The proof concatenates the adjacent-transposition words at the pivot. This
identity realizes Hankel moment arrays as off-diagonal entries of character Gram matrices.
-/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions.SymmetricCharacters

variable {X : Type*}

/-- Concatenating lists at one pivot concatenates their adjacent-transposition words. -/
theorem formPerm_append_pivot (xs ys : List X) (a : X) :
    (xs ++ a :: ys).formPerm = (xs ++ [a]).formPerm * (a :: ys).formPerm := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp [List.formPerm_cons_cons]
    | cons y xs =>
      simpa only [List.cons_append, List.formPerm_cons_cons, mul_assoc] using
        congrArg (fun p : Equiv.Perm X => Equiv.swap x y * p) ih

/-- The inverse-product word reverses the first arm and joins it to the second at the pivot. -/
theorem formPerm_pivot_inv_mul (xs ys : List X) (a : X) :
    (a :: xs).formPerm⁻¹ * (a :: ys).formPerm =
      (xs.reverse ++ a :: ys).formPerm := by
  rw [← List.formPerm_reverse, List.reverse_cons]
  exact (formPerm_append_pivot xs.reverse ys a).symm

variable [Fintype X]

/-- The multiplicative cycle class function; `p n` is the value of an `(n+1)`-cycle. -/
def cycleMomentCharacter (p : ℕ → ℝ) (σ : Equiv.Perm X) : ℝ :=
  (σ.cycleType.map (fun k => p (k - 1))).prod

theorem cycleMomentCharacter_one (p : ℕ → ℝ) :
    cycleMomentCharacter p (1 : Equiv.Perm X) = 1 := by
  simp [cycleMomentCharacter]

theorem cycleMomentCharacter_conj (p : ℕ → ℝ) (σ τ : Equiv.Perm X) :
    cycleMomentCharacter p (τ * σ * τ⁻¹) = cycleMomentCharacter p σ := by
  simp only [cycleMomentCharacter, Equiv.Perm.cycleType_conj]

/-- A nonempty list without repetitions describes precisely one cyclic block. -/
theorem cycleMomentCharacter_formPerm (p : ℕ → ℝ) (hp : p 0 = 1)
    (l : List X) (hl : l.Nodup) (hne : l ≠ []) :
    cycleMomentCharacter p l.formPerm = p (l.length - 1) := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a xs =>
    cases xs with
    | nil => simp [cycleMomentCharacter, hp]
    | cons b xs =>
      have hcycle := (List.isCycle_formPerm hl (by simp)).cycleType
      have hsupport := List.support_formPerm_of_nodup (a :: b :: xs) hl
        (fun z hz => by have := congrArg List.length hz; simp at this)
      rw [cycleMomentCharacter, hcycle, hsupport, List.card_toFinset,
        List.dedup_eq_self.mpr hl]
      simp

/-- Disjoint arms give the Hankel index: their lengths add. Empty arms are allowed. -/
theorem cycleMomentCharacter_commonPivot (p : ℕ → ℝ) (hp : p 0 = 1)
    (xs ys : List X) (a : X) (hl : (xs.reverse ++ a :: ys).Nodup) :
    cycleMomentCharacter p ((a :: xs).formPerm⁻¹ * (a :: ys).formPerm) =
      p (xs.length + ys.length) := by
  have hne : xs.reverse ++ a :: ys ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_append, List.length_reverse, List.length_cons,
      List.length_nil] at hlen
    omega
  rw [formPerm_pivot_inv_mul, cycleMomentCharacter_formPerm p hp _ hl hne]
  congr 1
  simp only [List.length_append, List.length_reverse, List.length_cons]
  omega

section TaggedArms
variable {I : Type*}

/-- Each arm has its own tag; `none` is the common pivot. -/
def pivotArm (r : I → ℕ) (i : I) : List (Option (Σ j, Fin (r j))) :=
  List.ofFn fun a : Fin (r i) => some ⟨i, a⟩

theorem pivotArm_length (r : I → ℕ) (i : I) : (pivotArm r i).length = r i := by
  simp [pivotArm]

theorem pivotArm_nodup (r : I → ℕ) (i : I) : (pivotArm r i).Nodup := by
  rw [pivotArm, List.nodup_ofFn]
  intro a b h
  simpa using h

theorem none_not_mem_pivotArm (r : I → ℕ) (i : I) : none ∉ pivotArm r i := by
  simp [pivotArm]

theorem pivotArms_nodup (r : I → ℕ) {i j : I} (hij : i ≠ j) :
    ((pivotArm r i).reverse ++ none :: pivotArm r j).Nodup := by
  have hr : (pivotArm r i).reverse.Nodup := List.nodup_reverse.mpr (pivotArm_nodup r i)
  refine List.nodup_append.mpr ⟨hr,
    List.nodup_cons.mpr ⟨none_not_mem_pivotArm r j, pivotArm_nodup r j⟩, ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, ha⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
  rcases List.mem_cons.mp hy with hy | hy
  · have hh := ha.trans (hxy.trans hy)
    cases hh
  · obtain ⟨b, hb⟩ := List.mem_ofFn.mp hy
    exact hij (congrArg Sigma.fst (Option.some.inj (ha.trans (hxy.trans hb.symm))))

/-- The cycle visiting the common pivot followed by a tagged arm. -/
def pivotPermutation (r : I → ℕ) (i : I) : Equiv.Perm (Option (Σ j, Fin (r j))) :=
  @List.formPerm _ (Classical.decEq _) (none :: pivotArm r i)

/-- Distinct tagged arms realize the desired Hankel entry in a character Gram matrix. -/
theorem cycleMomentCharacter_pivot_inv_mul [Fintype I]
    (p : ℕ → ℝ) (hp : p 0 = 1) (r : I → ℕ) (i j : I) :
    cycleMomentCharacter p ((pivotPermutation r i)⁻¹ * pivotPermutation r j) =
      if i = j then 1 else p (r i + r j) := by
  by_cases hij : i = j
  · subst j
    simp [cycleMomentCharacter_one]
  · rw [if_neg hij]
    simpa only [pivotPermutation, pivotArm_length] using
      cycleMomentCharacter_commonPivot p hp (pivotArm r i) (pivotArm r j) none
        (pivotArms_nodup r hij)

end TaggedArms

section GramMatrices
variable {I : Type*} [Fintype I]

/-- Gram matrix of cycles whose independently tagged arms share one pivot. -/
def pivotGram (p : ℕ → ℝ) (r : I → ℕ) (n : ℕ) :
    Matrix (I × Fin n) (I × Fin n) ℝ :=
  fun i j => cycleMomentCharacter p
    ((pivotPermutation (fun k : I × Fin n => r k.1) i)⁻¹ *
      pivotPermutation (fun k : I × Fin n => r k.1) j)

/-- The pivot Gram matrix is exactly the replicated Hankel kernel with unit diagonal. -/
theorem pivotGram_eq_replicatedKernel (p : ℕ → ℝ) (hp : p 0 = 1)
    (r : I → ℕ) (n : ℕ) :
    pivotGram p r n = replicatedKernel (fun i j => p (r i + r j))
      (fun i => 1 - p (r i + r i)) n := by
  ext i j
  rw [pivotGram, cycleMomentCharacter_pivot_inv_mul p hp]
  simp only [replicatedKernel, Matrix.add_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- All common-pivot Gram tests recover precisely Hankel positivity and the diagonal bound. -/
theorem forall_pivotGram_posSemidef_iff (p : ℕ → ℝ) (hp : p 0 = 1) (r : I → ℕ) :
    (∀ n, (pivotGram p r n).PosSemidef) ↔
      Matrix.PosSemidef (fun i j => p (r i + r j)) ∧ ∀ i, p (r i + r i) ≤ 1 := by
  simp_rw [pivotGram_eq_replicatedKernel p hp]
  exact forall_normalizedReplicas_posSemidef_iff _

end GramMatrices

/-- Positivity of the prescribed cycle class function on every finite symmetric group. -/
def PositiveCycleFamily (p : ℕ → ℝ) : Prop :=
  ∀ (X J : Type) [Fintype X] [Fintype J] (g : J → Equiv.Perm X),
    Matrix.PosSemidef (fun i j => cycleMomentCharacter p ((g i)⁻¹ * g j))

/-- Character positivity supplies the entire Hankel moment condition without a classification theorem. -/
theorem PositiveCycleFamily.hankel {p : ℕ → ℝ} (h : PositiveCycleFamily p)
    (hp : p 0 = 1) (N : ℕ) :
    Matrix.PosSemidef (fun i j : Fin N => p (i.val + j.val)) := by
  apply ((forall_pivotGram_posSemidef_iff p hp (fun i : Fin N => i.val)).mp ?_).1
  intro n
  exact h _ _ (pivotPermutation (fun k : Fin N × Fin n => k.1.val))

end GaloisForLFunctions.SymmetricCharacters
