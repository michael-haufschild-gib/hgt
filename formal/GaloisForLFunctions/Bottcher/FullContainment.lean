/-
# Full-compact containment (mixed-tower / exclusion-dichotomy brick L1)

An open bounded set whose frontier lies in a *full* compact set (compact with connected
complement) is itself contained in that compact set.  The one-line topology behind it: the
complement `Kᶜ` is preconnected and, being covered by the disjoint opens `U` and
`(closure U)ᶜ` with no room on the frontier, must sit entirely in one of them; it cannot sit
in the bounded `U`, so it avoids `closure U`, i.e. `closure U ⊆ K`.

Corollary for filled Julia sets: `frontier (K₁) ⊆ K₂ ⟹ K₁ ⊆ K₂`.  This is the sound half of
the audited answer to open problem 5 (the exclusion dichotomy "fullness upgrades boundary
inclusion to full inclusion").  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BasinConnected

open Set Metric

namespace Bottcher

/-- **Full-compact containment.** If `K ⊆ ℂ` is compact with connected complement (a *full*
compact set) and `U` is open, bounded, with `frontier U ⊆ K`, then even `closure U ⊆ K`. -/
theorem closure_subset_of_full_of_frontier_subset {K U : Set ℂ}
    (hKcomp : IsCompact K) (hKfull : IsPreconnected Kᶜ)
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hfront : frontier U ⊆ K) : closure U ⊆ K := by
  -- `Kᶜ` is covered by the two disjoint opens `U` and `(closure U)ᶜ`.
  have hcover : Kᶜ ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_contra hxc
    rw [mem_union, not_or] at hxc
    obtain ⟨hxU, hxcl⟩ := hxc
    rw [not_mem_compl_iff] at hxcl
    -- `x ∈ closure U`, `x ∉ U = interior U`, so `x ∈ frontier U ⊆ K`, contradicting `x ∈ Kᶜ`.
    rw [← hUopen.interior_eq] at hxU
    exact hx (hfront ⟨hxcl, hxU⟩)
  have hdisj : Disjoint U (closure U)ᶜ := disjoint_compl_right_iff_subset.mpr subset_closure
  have hclopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  rcases hKfull.subset_or_subset hUopen hclopen hdisj hcover with hL | hR
  · -- `Kᶜ ⊆ U` is impossible: `Kᶜ` is unbounded (K compact) while `U` is bounded.
    exfalso
    obtain ⟨R, hR⟩ := hKcomp.isBounded.exists_norm_le
    obtain ⟨R', hR'⟩ := hUbdd.exists_norm_le
    set t : ℝ := max (max R R') 0 + 1 with ht
    have htR : R < t := by
      have : R ≤ max (max R R') 0 := le_trans (le_max_left R R') (le_max_left _ _)
      linarith
    have htR' : R' < t := by
      have : R' ≤ max (max R R') 0 := le_trans (le_max_right R R') (le_max_left _ _)
      linarith
    have htpos : 0 < t := by
      have : (0:ℝ) ≤ max (max R R') 0 := le_max_right _ _
      linarith
    have hp_norm : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have hpK : (t : ℂ) ∉ K := by
      intro hmem
      have := hR _ hmem
      rw [hp_norm] at this; linarith
    have hpU := hL hpK
    have := hR' _ hpU
    rw [hp_norm] at this; linarith
  · -- `Kᶜ ⊆ (closure U)ᶜ`, i.e. `closure U ⊆ K`.
    exact compl_subset_compl.mp hR

/-- **Full-compact containment (open form).** Same hypotheses, conclusion `U ⊆ K`. -/
theorem subset_of_full_of_frontier_subset {K U : Set ℂ}
    (hKcomp : IsCompact K) (hKfull : IsPreconnected Kᶜ)
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hfront : frontier U ⊆ K) : U ⊆ K :=
  subset_closure.trans
    (closure_subset_of_full_of_frontier_subset hKcomp hKfull hUopen hUbdd hfront)

/-- **Filled-Julia frontier containment.** If the Julia set `∂K₁ = frontier (filledJulia c₁)`
is contained in the filled Julia set `filledJulia c₂`, then `filledJulia c₁ ⊆ filledJulia c₂`.

This upgrades a boundary inclusion to a full inclusion using fullness of `K₂` — the sound half
of the exclusion dichotomy for the general both-connected q62 case. -/
theorem filledJulia_subset_of_frontier_subset {c₁ c₂ : ℂ}
    (hfront : frontier (filledJulia c₁) ⊆ filledJulia c₂) :
    filledJulia c₁ ⊆ filledJulia c₂ := by
  intro x hx
  by_cases hxi : x ∈ interior (filledJulia c₁)
  · -- Interior part: apply the containment lemma with `U := interior (filledJulia c₁)`.
    refine subset_of_full_of_frontier_subset (isCompact_filledJulia c₂)
      (isPreconnected_compl_filledJulia c₂) isOpen_interior
      ((isBounded_filledJulia c₁).subset interior_subset)
      (fun y hy => hfront (frontier_interior_subset hy)) hxi
  · -- Boundary part: `x ∈ K₁ \ interior K₁ = frontier K₁ ⊆ K₂`.
    apply hfront
    rw [(isClosed_filledJulia c₁).frontier_eq]
    exact ⟨hx, hxi⟩

end Bottcher
