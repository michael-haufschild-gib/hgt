import GaloisForLFunctions.HTGeometry.UniformJetPadding

/-!
# The dominant-class residue over an arbitrary finite index

A Gamma-field presentation is indexed by pairs — a `Γ`-power and a monomial of the corresponding
coefficient — so its natural index is a sigma type, not an interval.  The dominance argument never
used the interval structure: it needs a finite nonempty index and a lexicographic minimum, both of
which any `Fintype` provides.

Restating the dominant-class residue over an arbitrary finite index removes the flattening step
between the presentation data and the tube residue theorem.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **A finite nonempty family of integer data has a dominant member.** -/
theorem exists_dominant_shapeZ_index_fintype {ι : Type*} [Fintype ι] [Nonempty ι]
    (k a b : ι → ℤ) :
    ∃ β : ι, ∀ α : ι,
      (k α = k β ∧ a α = a β ∧ b α = b β)
        ∨ (k β < k α ∨ (k α = k β ∧ a α < a β) ∨ (k α = k β ∧ a α = a β ∧ b α < b β)) := by
  classical
  obtain ⟨β, -, hβ⟩ := Finset.exists_min_image (Finset.univ : Finset ι)
    (fun α => (toLex (k α, toLex (-a α, -b α)) : ℤ ×ₗ (ℤ ×ₗ ℤ)))
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  refine ⟨β, fun α => ?_⟩
  have hle := hβ α (Finset.mem_univ α)
  rw [Prod.Lex.le_iff] at hle
  rcases hle with hlt | ⟨heq, hle2⟩
  · have h1 : k β < k α := hlt
    exact Or.inr (Or.inl h1)
  · have h1 : k β = k α := heq
    rw [Prod.Lex.le_iff] at hle2
    rcases hle2 with hlt2 | ⟨heq2, hle3⟩
    · have h2 : -a β < -a α := hlt2
      exact Or.inr (Or.inr (Or.inl ⟨h1.symm, by omega⟩))
    · have h2 : -a β = -a α := heq2
      have h3 : -b β ≤ -b α := hle3
      rcases lt_or_eq_of_le h3 with hlt3 | heq3
      · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, by omega, by omega⟩))
      · exact Or.inl ⟨h1.symm, by omega, by omega⟩

/-- **The dominant class residue over an arbitrary finite index.** -/
theorem tubeLimit_sum_div_dominant_class_fintype {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (F : ι → ℝ → ℝ → ℂ) (k a b : ι → ℤ) (c : ι → ℂ) (β : ι)
    (hlim : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShapeZ σ (k α) (a α) (b α) t) (c α))
    (hdom : ∀ α, (k α = k β ∧ a α = a β ∧ b α = b β)
      ∨ (k β < k α ∨ (k α = k β ∧ a α < a β) ∨ (k α = k β ∧ a α = a β ∧ b α < b β))) :
    TubeLimit M (fun σ t => (∑ α : ι, F α σ t) / gammaShapeZ σ (k β) (a β) (b β) t)
      (∑ α ∈ Finset.univ.filter
        (fun α : ι => k α = k β ∧ a α = a β ∧ b α = b β), c α) := by
  classical
  have hterm : ∀ α : ι, TubeLimit M
      (fun σ t => F α σ t / gammaShapeZ σ (k β) (a β) (b β) t)
      (if (k α = k β ∧ a α = a β ∧ b α = b β) then c α else 0) := by
    intro α
    by_cases htie : k α = k β ∧ a α = a β ∧ b α = b β
    · rw [if_pos htie]
      obtain ⟨h1, h2, h3⟩ := htie
      refine (hlim α).congr (T₀ := 0) fun σ t hσ hσM ht => ?_
      rw [h1, h2, h3]
    · rw [if_neg htie]
      have hsub : k β < k α ∨ (k α = k β ∧ a α < a β)
          ∨ (k α = k β ∧ a α = a β ∧ b α < b β) := (hdom α).resolve_left htie
      have hmul := (hlim α).mul (tubeLimit_gammaShapeZ_ratio_zero hM hsub)
      rw [mul_zero] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hSα : gammaShapeZ σ (k α) (a α) (b α) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      have hSβ : gammaShapeZ σ (k β) (a β) (b β) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      field_simp
  have hsum := TubeLimit.finsetSum (Finset.univ : Finset ι) fun α _ => hterm α
  rw [← Finset.sum_filter] at hsum
  refine hsum.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  rw [Finset.sum_div]

/-- **The residue of a finite family of data over an arbitrary finite index.** -/
theorem exists_tubeLimit_dominant_class_fintype {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (F : ι → ℝ → ℝ → ℂ) (k a b : ι → ℤ) (c : ι → ℂ)
    (hlim : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShapeZ σ (k α) (a α) (b α) t) (c α)) :
    ∃ β : ι, TubeLimit M
      (fun σ t => (∑ α : ι, F α σ t) / gammaShapeZ σ (k β) (a β) (b β) t)
      (∑ α ∈ Finset.univ.filter
        (fun α : ι => k α = k β ∧ a α = a β ∧ b α = b β), c α) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shapeZ_index_fintype k a b
  exact ⟨β, tubeLimit_sum_div_dominant_class_fintype hM F k a b c β hlim hβ⟩

end

end GaloisForLFunctions.HTGeometry
