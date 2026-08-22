import GaloisForLFunctions.HTGeometry.SteinbergTWTCore
import GaloisForLFunctions.HTGeometry.SteinbergMatsumotoRelation

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n] [LinearOrder n]

omit [DecidableEq n] [LinearOrder n] in
/-- The rank-one factorization which turns a lower root into a Weyl factor followed by
positive and transposed roots.  This is the descent identity in Matsumoto's `TWT` proof. -/
theorem steinbergX_eq_weyl_upper_transpose {i j : n} (hij : i ≠ j) (a : Fˣ) :
    steinbergX hij (a : F)
      = steinbergWeyl hij a * steinbergX hij (-(a : F))
        * steinbergX (Ne.symm hij) ((a⁻¹ : Fˣ) : F) := by
  rw [steinbergWeyl]
  symm
  calc
    steinbergX hij (a : F) * steinbergX (Ne.symm hij) (-((a⁻¹ : Fˣ) : F))
        * steinbergX hij (a : F) * steinbergX hij (-(a : F))
        * steinbergX (Ne.symm hij) ((a⁻¹ : Fˣ) : F)
      = steinbergX hij (a : F) * steinbergX (Ne.symm hij) (-((a⁻¹ : Fˣ) : F))
        * (steinbergX hij (a : F) * steinbergX hij (-(a : F)))
        * steinbergX (Ne.symm hij) ((a⁻¹ : Fˣ) : F) := by group
    _ = steinbergX hij (a : F) * steinbergX (Ne.symm hij) (-((a⁻¹ : Fˣ) : F))
        * steinbergX (Ne.symm hij) ((a⁻¹ : Fˣ) : F) := by
        rw [steinbergX_mul, add_neg_cancel, steinbergX_zero]
        group
    _ = steinbergX hij (a : F) := by
        rw [mul_assoc, steinbergX_mul, neg_add_cancel, steinbergX_zero, mul_one]

/-- A signed Weyl word sends a root generator into the upper subgroup exactly when its
underlying permutation preserves that root's orientation. -/
theorem weylWord_conj_root_mem_upper (word : SteinbergWeylWord F n)
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    {p q : n} (hpq : p ≠ q) (a : F) (hupper : word.perm p < word.perm q) :
    word.eval * steinbergX hpq a * word.eval⁻¹ ∈ upperSteinbergSubgroup (F := F) n := by
  rw [word.conj_root hspare hpq a]
  exact Subgroup.subset_closure
    ⟨word.perm p, word.perm q, word.perm.injective.ne_iff.mpr hpq,
      ((word.scale p : F) * ((word.scale q)⁻¹ : F) * a), hupper, rfl⟩

/-- Matsumoto's descent absorption step: appending the simple Weyl factor for a positive
root preserves `TWT` after any signed Weyl word. -/
theorem weylWord_upper_root_simpleWeyl_mem_TWT (word : SteinbergWeylWord F n)
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    {i j : n} (hij : i ≠ j) (hupper : i < j) (a : F) :
    word.eval * steinbergX hij a * steinbergWeyl hij 1 ∈ steinbergTWT (F := F) (n := n) := by
  rcases lt_or_gt_of_ne (word.perm.injective.ne_iff.mpr hij) with hforward | hbackward
  · have hconj := word.conj_root hspare hij a
    have hu : word.eval * steinbergX hij a * word.eval⁻¹
        ∈ upperSteinbergSubgroup (F := F) n := by
      rw [hconj]
      exact Subgroup.subset_closure
        ⟨word.perm i, word.perm j, word.perm.injective.ne_iff.mpr hij,
          ((word.scale i : F) * ((word.scale j)⁻¹ : F) * a), hforward, rfl⟩
    refine ⟨word.eval * steinbergX hij a * word.eval⁻¹, word.eval * steinbergWeyl hij 1, 1,
      hu, (steinbergWeylWordSubgroup (F := F) (n := n)).mul_mem
        (SteinbergWeylWord.eval_mem_subgroup word)
        (Subgroup.subset_closure ⟨i, j, hij, 1, rfl⟩),
      Subgroup.one_mem _, ?_⟩
    group
  · by_cases ha : a = 0
    · rw [ha, steinbergX_zero, mul_one]
      exact weyl_mem_steinbergTWT
        ((steinbergWeylWordSubgroup (F := F) (n := n)).mul_mem
          (SteinbergWeylWord.eval_mem_subgroup word)
          (Subgroup.subset_closure ⟨i, j, hij, 1, rfl⟩))
    · let b : Fˣ := Units.mk0 a ha
      let wp : SteinbergWeylWord F n := .snoc word i j hij b
      have hwp_eval : wp.eval = word.eval * steinbergWeyl hij b := by
        rfl
      have hwp_pos : wp.perm i < wp.perm j := by
        simpa [wp, SteinbergWeylWord.perm, Equiv.trans_apply] using hbackward
      have hwp_conj := wp.conj_root hspare hij (-(b : F))
      have hu : wp.eval * steinbergX hij (-(b : F)) * wp.eval⁻¹
          ∈ upperSteinbergSubgroup (F := F) n := by
        rw [hwp_conj]
        exact Subgroup.subset_closure
          ⟨wp.perm i, wp.perm j, wp.perm.injective.ne_iff.mpr hij,
            ((wp.scale i : F) * ((wp.scale j)⁻¹ : F) * (-(b : F))), hwp_pos, rfl⟩
      obtain ⟨m, him, hjm⟩ := hspare i j hij
      have hmove : steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F) * steinbergWeyl hij 1
          = steinbergWeyl hij 1 * steinbergX hij (-((b⁻¹ : Fˣ) : F)) := by
        simpa using steinbergTranspose_mul_weyl hij him hjm (1 : Fˣ) ((b⁻¹ : Fˣ) : F)
      refine ⟨wp.eval * steinbergX hij (-(b : F)) * wp.eval⁻¹,
        wp.eval * steinbergWeyl hij 1, steinbergX hij (-((b⁻¹ : Fˣ) : F)), hu,
        (steinbergWeylWordSubgroup (F := F) (n := n)).mul_mem
          (SteinbergWeylWord.eval_mem_subgroup wp)
          (Subgroup.subset_closure ⟨i, j, hij, 1, rfl⟩),
        Subgroup.subset_closure ⟨i, j, hij, -((b⁻¹ : Fˣ) : F), hupper, rfl⟩, ?_⟩
      rw [← show (b : F) = a by simp [b], steinbergX_eq_weyl_upper_transpose hij b]
      calc
        word.eval * (steinbergWeyl hij b * steinbergX hij (-(b : F))
            * steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F)) * steinbergWeyl hij 1
          = word.eval * steinbergWeyl hij b * steinbergX hij (-(b : F))
              * ((word.eval * steinbergWeyl hij b)⁻¹)
              * ((word.eval * steinbergWeyl hij b) * steinbergWeyl hij 1)
              * steinbergX hij (-((b⁻¹ : Fˣ) : F)) := by
              rw [show word.eval * (steinbergWeyl hij b * steinbergX hij (-(b : F))
                  * steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F)) * steinbergWeyl hij 1
                    = word.eval * steinbergWeyl hij b * steinbergX hij (-(b : F))
                      * (steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F)
                        * steinbergWeyl hij 1) by group, hmove]
              group
        _ = wp.eval * steinbergX hij (-(b : F)) * wp.eval⁻¹
              * (wp.eval * steinbergWeyl hij 1)
              * steinbergX hij (-((b⁻¹ : Fˣ) : F)) := by rw [← hwp_eval]

end GaloisForLFunctions.HTGeometry
