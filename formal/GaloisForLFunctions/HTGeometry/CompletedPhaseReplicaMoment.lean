import GaloisForLFunctions.HTGeometry.ReplicaContentPermutation

/-!
# The completed-phase replica moment of a flat seed

A content class is the image of the slot-permutation group, so it has at most `r!` members.  The
phase-completed replica moment of a flat seed against a target is the content-class-weighted sum of
the target's replica weights, and replacing every class size by `r!` turns that sum into `r!` times
the `r`-th power of the target's total weight.  For a unit target on a `D`-dimensional seed space
this is the bound `r!/D^r`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Steinhaus

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A content class has at most `r!` members: it is the image of the slot-permutation group. -/
theorem card_symClass_le_factorial (r : ℕ) (x : Fin r → α) :
    (symClass r x).card ≤ r.factorial := by
  classical
  have hsurj : ∀ y ∈ symClass r x, ∃ sigma ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))),
      x ∘ sigma = y := by
    intro y hy
    obtain ⟨sigma, hsig⟩ :=
      exists_perm_of_symTupleIndex_eq r ((mem_symClass_iff r x y).mp hy).symm
    exact ⟨sigma, Finset.mem_univ sigma, hsig.symm⟩
  have hcard := Finset.card_le_card_of_surjOn (fun sigma : Equiv.Perm (Fin r) => x ∘ sigma)
    (fun y hy => by
      obtain ⟨sigma, _, hsig⟩ := hsurj y hy
      exact ⟨sigma, Finset.mem_coe.mpr (Finset.mem_univ sigma), hsig⟩)
  calc (symClass r x).card ≤ (Finset.univ : Finset (Equiv.Perm (Fin r))).card := hcard
    _ = r.factorial := by
        rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- The replica weight of a coordinate factorizes over the slots. -/
theorem sum_prod_weight (r : ℕ) (p : α → ℝ) :
    (∑ x : Fin r → α, ∏ i, p (x i)) = (∑ a, p a) ^ r := by
  classical
  have h : (∑ x : Fin r → α, ∏ i, p (x i)) = ∏ _i : Fin r, ∑ a, p a := by
    rw [← Fintype.piFinset_univ,
      ← Finset.prod_univ_sum (fun _ : Fin r => (Finset.univ : Finset α)) (fun _ a => p a)]
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`(15)`.**  The content-class-weighted replica sum is at most `r!` times the `r`-th power of
the total weight. -/
theorem sum_symClass_card_mul_prod_le (r : ℕ) (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    (∑ x : Fin r → α, ((symClass r x).card : ℝ) * ∏ i, p (x i))
      ≤ (r.factorial : ℝ) * (∑ a, p a) ^ r := by
  classical
  have hprodnn : ∀ x : Fin r → α, 0 ≤ ∏ i, p (x i) := fun x =>
    Finset.prod_nonneg fun i _ => hp (x i)
  have hstep : (∑ x : Fin r → α, ((symClass r x).card : ℝ) * ∏ i, p (x i))
      ≤ ∑ x : Fin r → α, (r.factorial : ℝ) * ∏ i, p (x i) := by
    refine Finset.sum_le_sum fun x _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (hprodnn x)
    exact_mod_cast card_symClass_le_factorial r x
  rw [← Finset.mul_sum, sum_prod_weight] at hstep
  exact hstep

/-- **`(14)`--`(16)`.**  The completed-phase replica moment of a flat seed against a unit target is
at most `r!/D^r`. -/
theorem completedPhaseReplicaMoment_le (r : ℕ) [Nonempty α] (z : α → ℂ)
    (hz : ∑ a, ‖z a‖ ^ 2 ≤ 1) :
    (∑ x : Fin r → α, ((symClass r x).card : ℝ) *
        ∏ i, (‖z (x i)‖ ^ 2 / (Fintype.card α : ℝ)))
      ≤ (r.factorial : ℝ) / (Fintype.card α : ℝ) ^ r := by
  classical
  have hDpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have := Fintype.card_pos (α := α)
    exact_mod_cast this
  set p : α → ℝ := fun a => ‖z a‖ ^ 2 / (Fintype.card α : ℝ) with hp
  have hpnn : ∀ a, 0 ≤ p a := fun a => by
    rw [hp]
    positivity
  have hpsum : ∑ a, p a ≤ (Fintype.card α : ℝ)⁻¹ := by
    rw [hp, ← Finset.sum_div, div_le_iff₀ hDpos]
    calc ∑ a, ‖z a‖ ^ 2 ≤ 1 := hz
      _ = (Fintype.card α : ℝ)⁻¹ * (Fintype.card α : ℝ) := by
          rw [inv_mul_cancel₀ (ne_of_gt hDpos)]
  have hmain := sum_symClass_card_mul_prod_le r p hpnn
  have hpow : (∑ a, p a) ^ r ≤ ((Fintype.card α : ℝ)⁻¹) ^ r :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => hpnn a) hpsum r
  have hfac : (0 : ℝ) ≤ (r.factorial : ℝ) := by positivity
  calc (∑ x : Fin r → α, ((symClass r x).card : ℝ) * ∏ i, p (x i))
      ≤ (r.factorial : ℝ) * (∑ a, p a) ^ r := hmain
    _ ≤ (r.factorial : ℝ) * ((Fintype.card α : ℝ)⁻¹) ^ r := mul_le_mul_of_nonneg_left hpow hfac
    _ = (r.factorial : ℝ) / (Fintype.card α : ℝ) ^ r := by
        rw [inv_pow, ← div_eq_mul_inv]

end Steinhaus

end

end GaloisForLFunctions.HTGeometry
