import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm

/-!
# The projective tensor seminorm and quotients

If every element of `F'` lifts along `π : F → F'` with almost the same seminorm — the defining
property of a quotient seminorm — then the same holds for the projective tensor seminorms: every
element of `E ⊗ F'` lifts along `1 ⊗ π` with almost the same projective seminorm.

So tensoring by `E` carries a strict surjection to a strict surjection: the projective seminorm of
the quotient is the quotient of the projective seminorm.

* `exists_lifted_list` : a representation of a tensor lifts termwise at controlled cost.
* `exists_lift_projTensorSeminorm` : **`1 ⊗ π` lifts elements with almost the same seminorm.**
* `projTensorSeminorm_quotient_eq` : **the projective seminorm on the target is the infimum over
  lifts** — the tensored surjection is strict.
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E F F' : Type*} [NormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [AddCommGroup F'] [Module 𝕜 F']

/-! ## Lifting a representation -/

/-- If every vector lifts along `π` with almost the same seminorm, then so does every list of
pure tensors, at a cost controlled by the total weight of the first components. -/
theorem exists_lifted_list (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (q' : Seminorm 𝕜 F')
    (π : F →ₗ[𝕜] F') (hπ : ∀ (y' : F') (ε : ℝ), 0 < ε → ∃ y, π y = y' ∧ q y ≤ q' y' + ε)
    {δ : ℝ} (hδ : 0 < δ) (l : List (E × F')) :
    ∃ m : List (E × F),
      TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) π ((m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum)
          = (l.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum ∧
        projTensorSum p q m ≤ projTensorSum p q' l + δ * (l.map fun xy => p xy.1).sum := by
  induction l with
  | nil =>
    refine ⟨[], by simp, ?_⟩
    simp [projTensorSum]
  | cons a l ih =>
    obtain ⟨m, hm, hcost⟩ := ih
    obtain ⟨y, hy, hqy⟩ := hπ a.2 δ hδ
    refine ⟨(a.1, y) :: m, ?_, ?_⟩
    · have hsum : (((a.1, y) :: m).map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum
          = a.1 ⊗ₜ[𝕜] y + (m.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum := by
        simp
      rw [hsum, map_add, TensorProduct.map_tmul, LinearMap.id_apply, hy, hm]
      simp
    · have hcons : ∀ (P : Seminorm 𝕜 E) (Q : Seminorm 𝕜 F) (b : E × F) (n : List (E × F)),
          projTensorSum P Q (b :: n) = P b.1 * Q b.2 + projTensorSum P Q n := by
        intro P Q b n
        simp [projTensorSum]
      have hcons' : ∀ (P : Seminorm 𝕜 E) (Q : Seminorm 𝕜 F') (b : E × F') (n : List (E × F')),
          projTensorSum P Q (b :: n) = P b.1 * Q b.2 + projTensorSum P Q n := by
        intro P Q b n
        simp [projTensorSum]
      have hhead : p a.1 * q y ≤ p a.1 * q' a.2 + δ * p a.1 := by
        have hnn : (0 : ℝ) ≤ p a.1 := apply_nonneg p a.1
        nlinarith [hqy]
      have hlist : ((a :: l).map fun xy : E × F' => p xy.1).sum
          = p a.1 + (l.map fun xy : E × F' => p xy.1).sum := by
        simp
      rw [hcons, hcons', hlist]
      have hdist : δ * (p a.1 + (l.map fun xy : E × F' => p xy.1).sum)
          = δ * p a.1 + δ * (l.map fun xy : E × F' => p xy.1).sum := by ring
      rw [hdist]
      linarith

/-! ## Lifting a tensor -/

omit [AddCommGroup F'] [Module 𝕜 F'] in
/-- The total weight of the first components of a list is nonnegative. -/
theorem projTensorWeight_nonneg (p : Seminorm 𝕜 E) (l : List (E × F')) :
    0 ≤ (l.map fun xy : E × F' => p xy.1).sum := by
  refine List.sum_nonneg fun r hr => ?_
  simp only [List.mem_map, Prod.exists] at hr
  obtain ⟨x, y, _, hxy⟩ := hr
  rw [← hxy]
  exact apply_nonneg p x

theorem exists_pos_mul_le {S ε : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ * S ≤ ε := by
  refine ⟨ε / (1 + S), by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- **A tensor over the target lifts with almost the same projective seminorm.** -/
theorem exists_lift_projTensorSeminorm (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (q' : Seminorm 𝕜 F')
    (π : F →ₗ[𝕜] F') (hπ : ∀ (y' : F') (ε : ℝ), 0 < ε → ∃ y, π y = y' ∧ q y ≤ q' y' + ε)
    (w : E ⊗[𝕜] F') {ε : ℝ} (hε : 0 < ε) :
    ∃ z : E ⊗[𝕜] F, TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) π z = w ∧
      projTensorSeminorm p q z ≤ projTensorSeminorm p q' w + ε := by
  obtain ⟨l, hlsum, hl⟩ := exists_projTensorSum_lt p q' w
    (a := projTensorSeminorm p q' w + ε / 2) (by linarith)
  obtain ⟨δ, hδ, hδS⟩ :=
    exists_pos_mul_le (S := (l.map fun xy : E × F' => p xy.1).sum) (ε := ε / 2)
      (projTensorWeight_nonneg p l) (by linarith)
  obtain ⟨m, hmap, hcost⟩ := exists_lifted_list p q q' π hπ hδ l
  have hmapw : TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) π
      ((m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum) = w := by
    rw [hmap, hlsum]
  refine ⟨(m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum, hmapw, ?_⟩
  have hle := projTensorSeminorm_le_projTensorSum p q m
  linarith

/-! ## The tensored surjection is strict -/

/-- **The projective seminorm on the target is the infimum of the projective seminorms of the
lifts**: tensoring carries a strict surjection to a strict surjection. -/
theorem projTensorSeminorm_quotient_eq (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (q' : Seminorm 𝕜 F')
    (π : F →ₗ[𝕜] F') (hπ : ∀ (y' : F') (ε : ℝ), 0 < ε → ∃ y, π y = y' ∧ q y ≤ q' y' + ε)
    (hle : ∀ y : F, q' (π y) ≤ q y) (w : E ⊗[𝕜] F') :
    projTensorSeminorm p q' w
      = sInf {r : ℝ | ∃ z : E ⊗[𝕜] F,
          TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) π z = w ∧ projTensorSeminorm p q z = r} := by
  set T : Set ℝ := {r : ℝ | ∃ z : E ⊗[𝕜] F,
      TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) π z = w ∧ projTensorSeminorm p q z = r} with hT
  have hne : T.Nonempty := by
    obtain ⟨z, hz, _⟩ := exists_lift_projTensorSeminorm p q q' π hπ w (ε := 1) one_pos
    exact ⟨projTensorSeminorm p q z, ⟨z, hz, rfl⟩⟩
  have hbdd : BddBelow T := by
    refine ⟨projTensorSeminorm p q' w, ?_⟩
    rintro r ⟨z, hz, rfl⟩
    have hmap := projTensorSeminorm_map_le p q p q' (LinearMap.id : E →ₗ[𝕜] E) π
      zero_le_one zero_le_one (fun x => by rw [LinearMap.id_apply, one_mul])
      (fun y => by rw [one_mul]; exact hle y) z
    rw [hz, one_mul, one_mul] at hmap
    exact hmap
  refine le_antisymm ?_ ?_
  · refine le_csInf hne ?_
    rintro r ⟨z, hz, rfl⟩
    have hmap := projTensorSeminorm_map_le p q p q' (LinearMap.id : E →ₗ[𝕜] E) π
      zero_le_one zero_le_one (fun x => by rw [LinearMap.id_apply, one_mul])
      (fun y => by rw [one_mul]; exact hle y) z
    rw [hz, one_mul, one_mul] at hmap
    exact hmap
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz, hcost⟩ := exists_lift_projTensorSeminorm p q q' π hπ w hε
    exact le_trans (csInf_le hbdd ⟨z, hz, rfl⟩) hcost

end GaloisForLFunctions

end
