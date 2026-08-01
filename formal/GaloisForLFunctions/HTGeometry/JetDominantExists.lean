import GaloisForLFunctions.HTGeometry.JetMonomialNormalization

/-!
# A dominant datum always exists

The jet data are pairs of natural numbers ordered by argument degree first — smaller dominates —
and log degree second — larger dominates.  A finite nonempty family therefore has a dominant member:
minimize the argument degree, then maximize the log degree among the minimizers.

So the residue law needs no hypothesis on the family: every finite combination of jet monomials has
a datum by which to normalize, and the normalized combination converges to the sum of the leading
constants over the members sharing it.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **A finite family of jet monomials has a dominant member.** -/
theorem exists_dominant_index {N n : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) :
    ∃ β : Fin N, ∀ α : Fin N, (e α 0 = e β 0 ∧ jetSDeg (e α) = jetSDeg (e β))
      ∨ (jetSDeg (e β) < jetSDeg (e α)
        ∨ (jetSDeg (e β) = jetSDeg (e α) ∧ e α 0 < e β 0)) := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨β₀, -, hβ₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N))
    (fun α => jetSDeg (e α)) Finset.univ_nonempty
  set S : Finset (Fin N) :=
    Finset.univ.filter (fun α => jetSDeg (e α) = jetSDeg (e β₀)) with hS
  have hβ₀S : β₀ ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  obtain ⟨β, hβS, hβ⟩ := Finset.exists_max_image S (fun α => e α 0) ⟨β₀, hβ₀S⟩
  have hβdeg : jetSDeg (e β) = jetSDeg (e β₀) := by
    rw [hS, Finset.mem_filter] at hβS
    exact hβS.2
  refine ⟨β, fun α => ?_⟩
  have hmin : jetSDeg (e β₀) ≤ jetSDeg (e α) := hβ₀ α (Finset.mem_univ _)
  rcases eq_or_lt_of_le hmin with heq | hlt
  · have hαS : α ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, heq.symm⟩
    have hle : e α 0 ≤ e β 0 := hβ α hαS
    rcases eq_or_lt_of_le hle with h0 | h0
    · exact Or.inl ⟨h0, by rw [hβdeg, heq]⟩
    · exact Or.inr (Or.inr ⟨by rw [hβdeg, heq], h0⟩)
  · exact Or.inr (Or.inl (by rw [hβdeg]; exact hlt))

/-- **Eq. (19), unconditionally.**  Every finite nonempty combination of digamma jet monomials has a
normalization datum for which the combination converges, and the limit is the explicit sum of the
jet leading constants over the members sharing that datum. -/
theorem exists_datum_tendsto_sum_jetMonomial (hσ : 0 < σ) {n N : ℕ} (hN : 0 < N) (d : Fin N → ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) :
    ∃ β : Fin N, Tendsto (fun t : ℝ => (∑ α : Fin N, d α * jetMonomial σ (e α) t)
        / jetNormFactor σ (e β 0) (jetSDeg (e β)) t) atTop
      (nhds (∑ α ∈ Finset.univ.filter
          (fun α : Fin N => e α 0 = e β 0 ∧ jetSDeg (e α) = jetSDeg (e β)),
        d α * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_index hN e
  exact ⟨β, tendsto_sum_jetMonomial_div_dominant hσ d e β hβ⟩

end GaloisForLFunctions
