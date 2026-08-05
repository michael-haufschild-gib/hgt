import GaloisForLFunctions.HTGeometry.ExpandedEvaluationSetSampling

/-!
# Extending a full-rank node packet to a larger row family

The sampling construction produces exactly as many nodes as there are columns.  Every consumer of
the full-rank datum instead carries a fixed finite row family, only requiring that it be at least as
large as the column family.  The two are reconciled by two elementary facts:

* extra rows never destroy injectivity of the evaluation map, since a square subfamily already
  detects it;
* an injective node packet with values in an infinite region extends, injectively and inside the
  region, to any larger finite row family.

Consequently the full-rank datum on a row family is available as soon as the row family admits an
injection from the column family — the region being infinite, as an open region always is.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-! ## Extra rows are harmless -/

/-- Row selection cannot create injectivity: if a selected square subfamily already separates
coefficient vectors, so does the full matrix. -/
theorem mulVec_injective_of_submatrix_row {row N K : Type*} [Fintype N]
    [NonUnitalNonAssocSemiring K] (M : Matrix row N K) (f : N → row)
    (h : Function.Injective (M.submatrix f id).mulVec) : Function.Injective M.mulVec := by
  intro u v huv
  refine h ?_
  funext i
  exact congrFun huv (f i)

/-! ## Extending the node packet -/

/-- **An injective packet inside an infinite region extends to any larger finite family.**  The
values outside the given part are drawn from the region with the already-used values removed. -/
theorem exists_injective_extension_mem {ι row : Type*} [Fintype ι] [Fintype row]
    (f : ι → row) (hf : Function.Injective f) {S : Set ℂ} (hS : S.Infinite)
    (z₀ : ι → ℂ) (hz₀ : Function.Injective z₀) (hmem : ∀ i, z₀ i ∈ S) :
    ∃ z : row → ℂ, Function.Injective z ∧ (∀ b, z b ∈ S) ∧ ∀ i, z (f i) = z₀ i := by
  classical
  have hTinf : (S \ Set.range z₀).Infinite := hS.sdiff (Set.finite_range z₀)
  let e : ℕ ↪ ↥(S \ Set.range z₀) := hTinf.natEmbedding
  let g : row → ℂ := fun b => ((e (Fintype.equivFin row b) : ↥(S \ Set.range z₀)) : ℂ)
  have hginj : Function.Injective g := by
    intro b₁ b₂ hb
    have : e (Fintype.equivFin row b₁) = e (Fintype.equivFin row b₂) := Subtype.ext hb
    exact (Fintype.equivFin row).injective (Fin.val_injective (e.injective this))
  have hgmem : ∀ b, g b ∈ S := fun b => ((e (Fintype.equivFin row b)).2).1
  have hgnot : ∀ b, g b ∉ Set.range z₀ := fun b => ((e (Fintype.equivFin row b)).2).2
  refine ⟨fun b => if h : b ∈ Set.range f then z₀ (Classical.choose h) else g b, ?_, ?_, ?_⟩
  · intro b₁ b₂ hb
    dsimp only at hb
    by_cases h₁ : b₁ ∈ Set.range f <;> by_cases h₂ : b₂ ∈ Set.range f
    · rw [dif_pos h₁, dif_pos h₂] at hb
      have hi := hz₀ hb
      have e₁ := Classical.choose_spec h₁
      have e₂ := Classical.choose_spec h₂
      rw [← e₁, ← e₂, hi]
    · rw [dif_pos h₁, dif_neg h₂] at hb
      exact absurd ⟨_, hb⟩ (hgnot b₂)
    · rw [dif_neg h₁, dif_pos h₂] at hb
      exact absurd ⟨_, hb.symm⟩ (hgnot b₁)
    · rw [dif_neg h₁, dif_neg h₂] at hb
      exact hginj hb
  · intro b
    dsimp only
    by_cases h : b ∈ Set.range f
    · rw [dif_pos h]; exact hmem _
    · rw [dif_neg h]; exact hgmem b
  · intro i
    dsimp only
    have h : f i ∈ Set.range f := ⟨i, rfl⟩
    rw [dif_pos h]
    exact congrArg z₀ (hf (Classical.choose_spec h))

/-! ## The row-family discharge -/

/-- **The full-rank datum on any sufficiently large row family.**  Algebraic independence of the
node coordinate and the jets on an infinite region produces an injective node packet on the whole
row family, taking values in the region, whose expanded evaluation map is injective. -/
theorem exists_row_packet_mem_of_algebraicIndependent_restrict {κ row : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype row] {n q : ℕ} {F : Fin n → ℂ → ℂ} {S : Set ℂ} (hS : S.Infinite)
    (halg : AlgebraicIndependent ℂ (fun i => Set.restrict S (jetEvaluationFamily F i)))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, z b ∈ S) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  obtain ⟨z₀, hz₀mem, hz₀inj, hz₀rank⟩ :=
    exists_node_packet_mem_of_algebraicIndependent_restrict (q := q) halg hexp
  obtain ⟨z, hzinj, hzmem, hzext⟩ :=
    exists_injective_extension_mem f hf hS z₀ hz₀inj hz₀mem
  refine ⟨z, hzmem, hzinj, ?_⟩
  refine mulVec_injective_of_submatrix_row _ f ?_
  have hsub :
      (expandedDifferentialEvaluationMatrix q n z exponent
          (fun p => F p.2 (z p.1))).submatrix f id
        = expandedDifferentialEvaluationMatrix q n z₀ exponent (fun p => F p.2 (z₀ p.1)) := by
    ext b c
    simp only [Matrix.submatrix_apply, id_eq]
    simp only [expandedDifferentialEvaluationMatrix, hzext]
  rw [hsub]
  exact hz₀rank

/-- **The upper half-plane form.**  This is the literal shape of the full-rank datum demanded by the
translation-rank genericity laws. -/
theorem exists_row_packet_upperHalfPlane_of_algebraicIndependent {κ row : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype row] {n q : ℕ} {F : Fin n → ℂ → ℂ}
    (halg : AlgebraicIndependent ℂ
      (fun i => Set.restrict upperHalfPlane (jetEvaluationFamily F i)))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  refine exists_row_packet_mem_of_algebraicIndependent_restrict ?_ halg hexp f hf
  refine Set.Infinite.mono (s := (fun t : ℝ => (⟨0, t⟩ : ℂ)) '' Set.Ioi (0 : ℝ)) ?_ ?_
  · rintro w ⟨t, ht, rfl⟩
    exact ht
  · refine Set.Infinite.image ?_ (Set.Ioi_infinite (0 : ℝ))
    intro s _ t _ hst
    exact congrArg Complex.im hst

end GaloisForLFunctions.HTGeometry
