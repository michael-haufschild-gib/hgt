import GaloisForLFunctions.HTGeometry.GammaJetShapeRatios

/-!
# A dominant Gamma-jet datum always exists

The data of a Gamma-field term are ordered on three levels: the Gamma exponent first — smaller
dominates — then the argument degree `deg p − b` — larger dominates — then the log degree — larger
dominates.  A finite nonempty family has a dominant member: minimize the Gamma exponent, maximize the
argument degree among the minimizers, and maximize the log degree among those.

Comparing argument degrees needs no integers in the statement: `deg p_α − b_α ≤ deg p_β − b_β` is
`deg p_α + b_β ≤ deg p_β + b_α`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- **A finite family of Gamma-jet data has a dominant member.** -/
theorem exists_dominant_gammaJet_index {N : ℕ} (hN : 0 < N) (u a dP b : Fin N → ℕ) :
    ∃ β : Fin N, ∀ α : Fin N,
      (u α = u β ∧ dP α + b β = dP β + b α ∧ a α = a β)
      ∨ (u β < u α)
      ∨ (u α = u β ∧ dP α + b β < dP β + b α)
      ∨ (u α = u β ∧ dP α + b β = dP β + b α ∧ a α < a β) := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨β₀, -, hβ₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) u
    Finset.univ_nonempty
  set S₁ : Finset (Fin N) := Finset.univ.filter (fun α => u α = u β₀) with hS₁
  have hβ₀S₁ : β₀ ∈ S₁ := by
    rw [hS₁, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  obtain ⟨β₁, hβ₁S₁, hβ₁⟩ := Finset.exists_max_image S₁
    (fun α => (dP α : ℤ) - (b α : ℤ)) ⟨β₀, hβ₀S₁⟩
  set S₂ : Finset (Fin N) :=
    S₁.filter (fun α => (dP α : ℤ) - (b α : ℤ) = (dP β₁ : ℤ) - (b β₁ : ℤ)) with hS₂
  have hβ₁S₂ : β₁ ∈ S₂ := by
    rw [hS₂, Finset.mem_filter]
    exact ⟨hβ₁S₁, rfl⟩
  obtain ⟨β, hβS₂, hβ⟩ := Finset.exists_max_image S₂ a ⟨β₁, hβ₁S₂⟩
  have hβS₁ : β ∈ S₁ := by
    rw [hS₂, Finset.mem_filter] at hβS₂
    exact hβS₂.1
  have hβu : u β = u β₀ := by
    rw [hS₁, Finset.mem_filter] at hβS₁
    exact hβS₁.2
  have hβdeg : (dP β : ℤ) - (b β : ℤ) = (dP β₁ : ℤ) - (b β₁ : ℤ) := by
    rw [hS₂, Finset.mem_filter] at hβS₂
    exact hβS₂.2
  refine ⟨β, fun α => ?_⟩
  have hmin : u β₀ ≤ u α := hβ₀ α (Finset.mem_univ _)
  rcases eq_or_lt_of_le hmin with heq | hlt
  · have hαS₁ : α ∈ S₁ := by
      rw [hS₁, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, heq.symm⟩
    have hdegle : (dP α : ℤ) - (b α : ℤ) ≤ (dP β : ℤ) - (b β : ℤ) := by
      rw [hβdeg]
      exact hβ₁ α hαS₁
    rcases eq_or_lt_of_le hdegle with hdeq | hdlt
    · have hαS₂ : α ∈ S₂ := by
        rw [hS₂, Finset.mem_filter]
        exact ⟨hαS₁, by rw [hdeq, hβdeg]⟩
      have hale : a α ≤ a β := hβ α hαS₂
      rcases eq_or_lt_of_le hale with haeq | halt
      · exact Or.inl ⟨by omega, by omega, haeq⟩
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, halt⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · exact Or.inr (Or.inl (by omega))

end GaloisForLFunctions
