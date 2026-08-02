import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm

/-!
# The projective tensor seminorm of a directed union

A tensor is a finite sum of pure tensors, so if the coefficient space is the directed union of
subspaces then every tensor already lives over one of them, and every representation of a tensor
uses only finitely many coefficients, hence lives over one of them too.  Consequently the projective
tensor seminorm of the union is the infimum of the projective tensor seminorms of the stages: the
tensor product carries the final topology of the stages — the strict pro-Ind topology.

* `exists_stage_of_list` : finitely many vectors lie in a common stage.
* `exists_stage_list_tensor` : a representation over the union is a representation over a stage,
  at the same cost.
* `exists_stage_tensor` : **every tensor comes from a stage.**
* `projTensorSeminorm_eq_sInf_stage` : **the seminorm of the union is the infimum over stages.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 M F ι : Type*} [NormedField 𝕜]
variable [AddCommGroup M] [Module 𝕜 M] [AddCommGroup F] [Module 𝕜 F]

/-! ## Finitely many vectors lie in a stage -/

theorem exists_stage_of_list [Nonempty ι] (E : ι → Submodule 𝕜 M)
    (hdir : Directed (· ≤ ·) E) (htop : ⨆ ν, E ν = ⊤) (l : List M) :
    ∃ ν : ι, ∀ x ∈ l, x ∈ E ν := by
  induction l with
  | nil =>
    obtain ⟨ν⟩ := ‹Nonempty ι›
    exact ⟨ν, fun x hx => absurd hx (List.not_mem_nil)⟩
  | cons a l ih =>
    obtain ⟨ν, hν⟩ := ih
    have hmem : a ∈ ⨆ μ, E μ := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_of_directed E hdir).mp hmem
    obtain ⟨κ, hκ1, hκ2⟩ := hdir ν μ
    refine ⟨κ, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hκ2 hμ
    · exact hκ1 (hν x hx')

/-! ## A representation over the union is one over a stage -/

theorem exists_stage_list_tensor (p : Seminorm 𝕜 M) (q : Seminorm 𝕜 F)
    (E : ι → Submodule 𝕜 M) (ν : ι) (l : List (M × F)) (hmem : ∀ xy ∈ l, xy.1 ∈ E ν) :
    ∃ m : List ((E ν) × F),
      TensorProduct.map (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F)
          ((m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum)
        = (l.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum ∧
      projTensorSum (p.comp (E ν).subtype) q m = projTensorSum p q l := by
  induction l with
  | nil =>
    refine ⟨[], by simp, by simp [projTensorSum]⟩
  | cons a l ih =>
    obtain ⟨m, hmap, hcost⟩ := ih (fun xy hxy => hmem xy (List.mem_cons_of_mem a hxy))
    refine ⟨(⟨a.1, hmem a (by simp)⟩, a.2) :: m, ?_, ?_⟩
    · have hsum : (((⟨a.1, hmem a (by simp)⟩, a.2) :: m).map
          fun xy : (E ν) × F => xy.1 ⊗ₜ[𝕜] xy.2).sum
          = (⟨a.1, hmem a (by simp)⟩ : E ν) ⊗ₜ[𝕜] a.2
            + (m.map fun xy : (E ν) × F => xy.1 ⊗ₜ[𝕜] xy.2).sum := by
        simp
      rw [hsum, map_add, TensorProduct.map_tmul, LinearMap.id_apply, hmap]
      simp
    · have hc1 : projTensorSum (p.comp (E ν).subtype) q ((⟨a.1, hmem a (by simp)⟩, a.2) :: m)
          = (p.comp (E ν).subtype) (⟨a.1, hmem a (by simp)⟩ : E ν) * q a.2
            + projTensorSum (p.comp (E ν).subtype) q m := by
        simp [projTensorSum]
      have hc2 : projTensorSum p q (a :: l) = p a.1 * q a.2 + projTensorSum p q l := by
        simp [projTensorSum]
      have hc3 : (p.comp (E ν).subtype) (⟨a.1, hmem a (by simp)⟩ : E ν) = p a.1 := by
        rw [Seminorm.comp_apply]
        rfl
      rw [hc1, hc2, hc3, hcost]

/-! ## Every tensor comes from a stage -/

/-- **Every tensor over a directed union comes from a stage.** -/
theorem exists_stage_tensor [Nonempty ι] (E : ι → Submodule 𝕜 M)
    (hdir : Directed (· ≤ ·) E) (htop : ⨆ ν, E ν = ⊤) (z : M ⊗[𝕜] F) :
    ∃ (ν : ι) (w : (E ν) ⊗[𝕜] F),
      TensorProduct.map (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F) w = z := by
  obtain ⟨l⟩ := nonempty_projTensorLift (𝕜 := 𝕜) (E := M) (F := F) z
  obtain ⟨ν, hν⟩ := exists_stage_of_list E hdir htop (l.1.map fun xy => xy.1)
  have hmem : ∀ xy ∈ l.1, xy.1 ∈ E ν := by
    intro xy hxy
    exact hν xy.1 (List.mem_map_of_mem hxy)
  obtain ⟨m, hmap, _⟩ :=
    exists_stage_list_tensor (0 : Seminorm 𝕜 M) (0 : Seminorm 𝕜 F) E ν l.1 hmem
  exact ⟨ν, (m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum, by rw [hmap, l.2]⟩

/-! ## The seminorm of the union is the infimum over stages -/

/-- **The projective seminorm of a directed union is the infimum of the stage seminorms**: the
tensor product carries the final topology of the stages. -/
theorem projTensorSeminorm_eq_sInf_stage [Nonempty ι] (p : Seminorm 𝕜 M) (q : Seminorm 𝕜 F)
    (E : ι → Submodule 𝕜 M) (hdir : Directed (· ≤ ·) E) (htop : ⨆ ν, E ν = ⊤)
    (z : M ⊗[𝕜] F) :
    projTensorSeminorm p q z
      = sInf {r : ℝ | ∃ (ν : ι) (w : (E ν) ⊗[𝕜] F),
          TensorProduct.map (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F) w = z ∧
            projTensorSeminorm (p.comp (E ν).subtype) q w = r} := by
  classical
  set T : Set ℝ := {r : ℝ | ∃ (ν : ι) (w : (E ν) ⊗[𝕜] F),
      TensorProduct.map (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F) w = z ∧
        projTensorSeminorm (p.comp (E ν).subtype) q w = r} with hT
  have hstage : ∀ (ν : ι) (w : (E ν) ⊗[𝕜] F),
      TensorProduct.map (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F) w = z →
      projTensorSeminorm p q z ≤ projTensorSeminorm (p.comp (E ν).subtype) q w := by
    intro ν w hw
    have hmap := projTensorSeminorm_map_le (p.comp (E ν).subtype) q p q
      (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F) zero_le_one zero_le_one
      (fun u => by rw [one_mul, Seminorm.comp_apply]) (fun f => by rw [one_mul]; exact le_rfl) w
    rw [hw, one_mul, one_mul] at hmap
    exact hmap
  have hne : T.Nonempty := by
    obtain ⟨ν, w, hw⟩ := exists_stage_tensor E hdir htop z
    exact ⟨projTensorSeminorm (p.comp (E ν).subtype) q w, ⟨ν, w, hw, rfl⟩⟩
  have hbdd : BddBelow T := by
    refine ⟨projTensorSeminorm p q z, ?_⟩
    rintro r ⟨ν, w, hw, rfl⟩
    exact hstage ν w hw
  refine le_antisymm (le_csInf hne ?_) ?_
  · rintro r ⟨ν, w, hw, rfl⟩
    exact hstage ν w hw
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨l, hlsum, hlcost⟩ := exists_projTensorSum_lt p q z
      (a := projTensorSeminorm p q z + ε) (by linarith)
    obtain ⟨ν, hν⟩ := exists_stage_of_list E hdir htop (l.map fun xy => xy.1)
    have hmem : ∀ xy ∈ l, xy.1 ∈ E ν := by
      intro xy hxy
      exact hν xy.1 (List.mem_map_of_mem hxy)
    obtain ⟨m, hmap, hcost⟩ := exists_stage_list_tensor p q E ν l hmem
    have hwz : TensorProduct.map (E ν).subtype (LinearMap.id : F →ₗ[𝕜] F)
        ((m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum) = z := by
      rw [hmap, hlsum]
    have hle : projTensorSeminorm (p.comp (E ν).subtype) q
        ((m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum) ≤ projTensorSum p q l := by
      refine le_trans (projTensorSeminorm_le_projTensorSum (p.comp (E ν).subtype) q m) ?_
      exact le_of_eq hcost
    refine le_trans (csInf_le hbdd ⟨ν, _, hwz, rfl⟩) ?_
    exact le_trans hle hlcost.le

end GaloisForLFunctions

end
