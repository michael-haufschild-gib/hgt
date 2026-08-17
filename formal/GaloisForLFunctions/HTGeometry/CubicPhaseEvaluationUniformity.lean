import GaloisForLFunctions.HTGeometry.ReedMullerEvaluationRank

/-!
# Cubic phase evaluations are uniform at fifteen points

The evaluation map of degree-at-most-three multilinear polynomials with coefficients in `ZMod 8` is
surjective at any fifteen distinct Boolean points, because its reduction modulo two is surjective --
that is the Reed--Muller rank statement -- and two is nilpotent modulo eight: a residual that is
even can be halved three times before it vanishes.

A surjective homomorphism of finite abelian groups has fibres of equal size, so the vector of
evaluations of a uniformly sampled cubic polynomial is uniform on `(ZMod 8)^k`.  The corresponding
eighth roots of unity are therefore independent uniform phases.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

/-! ## Lifting surjectivity from `ZMod 2` to `ZMod 8` -/

section Lift

variable {k : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

/-- Reduction of coefficients modulo two. -/
private abbrev redEight : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

theorem exists_two_mul_of_red_eq_zero {x : ZMod 8} (hx : redEight x = 0) :
    ∃ y : ZMod 8, x = 2 * y := by
  revert hx
  revert x
  decide

theorem red_lift (a : ZMod 2) : redEight ((a.val : ZMod 8)) = a := by
  revert a
  decide

theorem eight_eq_zero : (8 : ZMod 8) = 0 := by decide

omit [DecidableEq β] in
/-- One modular step: a residual solvable modulo two leaves an even remainder. -/
private theorem exists_mulVec_add_two_smul (A : Matrix (Fin k) β (ZMod 8))
    (hmod : Function.Surjective fun c : β → ZMod 2 => (A.map redEight) *ᵥ c)
    (w : Fin k → ZMod 8) :
    ∃ (c : β → ZMod 8) (w' : Fin k → ZMod 8), ∀ i, w i = (A *ᵥ c) i + 2 * w' i := by
  classical
  obtain ⟨cbar, hc⟩ := hmod fun i => redEight (w i)
  set c : β → ZMod 8 := fun b => ((cbar b).val : ZMod 8) with hcdef
  have hred : (redEight ∘ c) = cbar := by
    funext b
    rw [Function.comp_apply, hcdef, red_lift]
  have hres : ∀ i, redEight (w i - (A *ᵥ c) i) = 0 := by
    intro i
    have hmap := RingHom.map_mulVec redEight A c i
    rw [hred] at hmap
    have hci : ((A.map redEight) *ᵥ cbar) i = redEight (w i) := congrFun hc i
    rw [map_sub, hmap, hci, sub_self]
  choose y hy using fun i => exists_two_mul_of_red_eq_zero (hres i)
  refine ⟨c, y, fun i => ?_⟩
  have := hy i
  linear_combination (norm := ring_nf) this

omit [DecidableEq β] in
theorem mulVec_digits (A : Matrix (Fin k) β (ZMod 8)) (c₀ c₁ c₂ : β → ZMod 8) (i : Fin k) :
    (A *ᵥ fun b => c₀ b + 2 * c₁ b + 4 * c₂ b) i
      = (A *ᵥ c₀) i + 2 * (A *ᵥ c₁) i + 4 * (A *ᵥ c₂) i := by
  classical
  show (∑ b, A i b * (c₀ b + 2 * c₁ b + 4 * c₂ b))
      = (∑ b, A i b * c₀ b) + 2 * (∑ b, A i b * c₁ b) + 4 * (∑ b, A i b * c₂ b)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [DecidableEq β] in
/-- **Surjectivity lifts from `ZMod 2` to `ZMod 8`.**  Three halvings exhaust the nilpotent ideal. -/
theorem surjective_mulVec_of_surjective_map (A : Matrix (Fin k) β (ZMod 8))
    (hmod : Function.Surjective fun c : β → ZMod 2 => (A.map redEight) *ᵥ c) :
    Function.Surjective fun c : β → ZMod 8 => A *ᵥ c := by
  intro w
  obtain ⟨c₀, w₁, h₀⟩ := exists_mulVec_add_two_smul A hmod w
  obtain ⟨c₁, w₂, h₁⟩ := exists_mulVec_add_two_smul A hmod w₁
  obtain ⟨c₂, w₃, h₂⟩ := exists_mulVec_add_two_smul A hmod w₂
  refine ⟨fun b => c₀ b + 2 * c₁ b + 4 * c₂ b, ?_⟩
  funext i
  show (A *ᵥ fun b => c₀ b + 2 * c₁ b + 4 * c₂ b) i = w i
  rw [mulVec_digits]
  have hzero : (8 : ZMod 8) * w₃ i = 0 := by
    rw [eight_eq_zero, zero_mul]
  have hexp : w i = (A *ᵥ c₀) i + 2 * ((A *ᵥ c₁) i + 2 * ((A *ᵥ c₂) i + 2 * w₃ i)) := by
    rw [h₀ i, h₁ i, h₂ i]
  rw [hexp]
  linear_combination (norm := ring_nf) -hzero

end Lift

/-! ## Equal fibres of a surjective homomorphism -/

section Fibres

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H] [DecidableEq H]

omit [Fintype H] in
/-- All fibres of a surjective homomorphism of finite abelian groups have the same size. -/
theorem card_fiber_eq_card_kernel (fmap : G →+ H) (hf : Function.Surjective fmap) (w : H) :
    (univ.filter fun g => fmap g = w).card = (univ.filter fun g => fmap g = 0).card := by
  classical
  obtain ⟨c, hc⟩ := hf w
  refine Finset.card_nbij' (fun g => g - c) (fun g => g + c) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hg ⊢
    rw [map_sub, hg, hc, sub_self]
  · intro g hg
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hg ⊢
    rw [map_add, hg, hc, zero_add]
  · intro g _
    simp
  · intro g _
    simp

/-- **Uniformity.**  A surjective homomorphism of finite abelian groups sends the uniform
distribution to the uniform distribution: every fibre has size the quotient of the cardinalities. -/
theorem card_fiber_mul_card_eq_card (fmap : G →+ H) (hf : Function.Surjective fmap) (w : H) :
    (univ.filter fun g => fmap g = w).card * Fintype.card H = Fintype.card G := by
  classical
  have hpart : (univ : Finset G).card = ∑ h : H, (univ.filter fun g => fmap g = h).card :=
    Finset.card_eq_sum_card_fiberwise fun g _ => mem_univ (fmap g)
  have hconst : ∀ h : H, (univ.filter fun g => fmap g = h).card
      = (univ.filter fun g => fmap g = w).card := by
    intro h
    rw [card_fiber_eq_card_kernel fmap hf h, card_fiber_eq_card_kernel fmap hf w]
  rw [Finset.sum_congr rfl fun h _ => hconst h, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hpart
  rw [Finset.card_univ] at hpart
  rw [mul_comm]
  omega

end Fibres

/-! ## Theorem A: cubic evaluations are fifteen-wise uniform -/

section CubicPhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_reedMullerEvalMatrix {k m : ℕ} (x : Fin k → (ι → Bool)) :
    (reedMullerEvalMatrix (ZMod 8) m x).map redEight = reedMullerEvalMatrix (ZMod 2) m x := by
  classical
  funext j S
  rw [Matrix.map_apply, reedMullerEvalMatrix, reedMullerEvalMatrix]
  by_cases h : ∀ i ∈ S.1, x j i = true
  · rw [if_pos h, if_pos h, map_one]
  · rw [if_neg h, if_neg h, map_zero]

/-- **Surjective cubic evaluation over `ZMod 8`.**  Fewer than `2^(m+1)` distinct Boolean points
admit every prescribed vector of degree-at-most-`m` evaluations. -/
theorem surjective_mulVec_evalMatrix_zmod_eight {k m : ℕ} (hk : k < 2 ^ (m + 1))
    (x : Fin k → (ι → Bool)) (hx : Function.Injective x) :
    Function.Surjective fun c : MonLe ι m → ZMod 8 =>
      (reedMullerEvalMatrix (ZMod 8) m x) *ᵥ c := by
  refine surjective_mulVec_of_surjective_map _ ?_
  rw [map_reedMullerEvalMatrix]
  exact surjective_mulVec_evalMatrix hk x hx

/-- **Theorem A.**  At fewer than `2^(m+1)` distinct Boolean points the evaluation vector of a
uniformly sampled coefficient family is uniform: every value vector has the same number of
preimages, namely the coefficient count divided by the number of value vectors. -/
theorem card_fiber_evalMatrix_mul_card_eq {k m : ℕ} (hk : k < 2 ^ (m + 1))
    (x : Fin k → (ι → Bool)) (hx : Function.Injective x) (w : Fin k → ZMod 8) :
    (univ.filter fun c : MonLe ι m → ZMod 8 =>
        (reedMullerEvalMatrix (ZMod 8) m x) *ᵥ c = w).card * 8 ^ k
      = Fintype.card (MonLe ι m → ZMod 8) := by
  classical
  have hcard : Fintype.card (Fin k → ZMod 8) = 8 ^ k := by
    simp
  have hhom := card_fiber_mul_card_eq_card
    ((Matrix.mulVecLin (reedMullerEvalMatrix (ZMod 8) m x)).toAddMonoidHom)
    (surjective_mulVec_evalMatrix_zmod_eight hk x hx) w
  rw [hcard] at hhom
  exact hhom

end CubicPhase

end GaloisForLFunctions.HTGeometry
