import GaloisForLFunctions.HTGeometry.DatumToJetShape
import GaloisForLFunctions.HTGeometry.GammaJetRatioFamily
import GaloisForLFunctions.HTGeometry.GammaFieldShapeConvergence

/-!
# The datum of a finite sum with a dominant member

A finite sum of functions, each with a residue against its own shape, has a residue against the shape
of any chosen member: dividing termwise,

`(∑_α F_α)/S_β = ∑_α (F_α/S_α)·(S_α/S_β) → ∑_α c_α r_α`.

When `β` is dominant — `r_β = 1` and `r_α = 0` for the others — the limit is `c_β`, so the datum of
the sum is the datum of the dominant member.  This is the assembly step for a family of groups
separated by the `(s`-order, log-order`)` ordering.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- **The residue of a finite sum against one member's shape.** -/
theorem tendsto_sum_div_shape {N : ℕ} (F S : Fin N → ℝ → ℂ) (β : Fin N) (c r : Fin N → ℂ)
    (hS : ∀ α : Fin N, ∀ᶠ t : ℝ in atTop, S α t ≠ 0)
    (hres : ∀ α : Fin N, Tendsto (fun t : ℝ => F α t / S α t) atTop (nhds (c α)))
    (hrat : ∀ α : Fin N, Tendsto (fun t : ℝ => S α t / S β t) atTop (nhds (r α))) :
    Tendsto (fun t : ℝ => (∑ α : Fin N, F α t) / S β t) atTop (nhds (∑ α : Fin N, c α * r α)) := by
  classical
  have hterm : ∀ α : Fin N,
      Tendsto (fun t : ℝ => F α t / S β t) atTop (nhds (c α * r α)) := by
    intro α
    have hmul := (hres α).mul (hrat α)
    refine hmul.congr' ?_
    filter_upwards [hS α] with t ht
    field_simp
  have hsum := tendsto_finsetSum Finset.univ (fun α _ => hterm α)
  refine hsum.congr fun t => ?_
  rw [Finset.sum_div]

/-- **The datum of a sum is the datum of its dominant member.** -/
theorem tendsto_sum_div_dominant {N : ℕ} (F S : Fin N → ℝ → ℂ) (β : Fin N) (c : Fin N → ℂ)
    (hS : ∀ α : Fin N, ∀ᶠ t : ℝ in atTop, S α t ≠ 0)
    (hres : ∀ α : Fin N, Tendsto (fun t : ℝ => F α t / S α t) atTop (nhds (c α)))
    (hdom : ∀ α : Fin N, α ≠ β → Tendsto (fun t : ℝ => S α t / S β t) atTop (nhds 0)) :
    Tendsto (fun t : ℝ => (∑ α : Fin N, F α t) / S β t) atTop (nhds (c β)) := by
  classical
  have hself : Tendsto (fun t : ℝ => S β t / S β t) atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hS β] with t ht
    rw [div_self ht]
  have hrat : ∀ α : Fin N,
      Tendsto (fun t : ℝ => S α t / S β t) atTop (nhds (if α = β then 1 else 0)) := by
    intro α
    by_cases hα : α = β
    · subst hα
      rw [if_pos rfl]
      exact hself
    · rw [if_neg hα]
      exact hdom α hα
  have hsum := tendsto_sum_div_shape F S β c (fun α => if α = β then 1 else 0) hS hres hrat
  have hval : (∑ α : Fin N, c α * (if α = β then (1 : ℂ) else 0)) = c β := by
    have hcongr : ∀ α : Fin N, c α * (if α = β then (1 : ℂ) else 0)
        = if α = β then c α else 0 := by
      intro α
      by_cases hα : α = β
      · rw [if_pos hα, if_pos hα, mul_one]
      · rw [if_neg hα, if_neg hα, mul_zero]
    rw [Finset.sum_congr rfl (fun α _ => hcongr α), Finset.sum_ite_eq' Finset.univ β c,
      if_pos (Finset.mem_univ β)]
  rwa [hval] at hsum

/-- **The separation criterion for two shapes.**  A shape is subordinate to another when it decays
faster in `s`, or decays equally and carries a lower power of the logarithm. -/
theorem tendsto_polyJetShape_ratio_zero_of_pair {σ : ℝ} (hσ : 0 < σ) {a₁ b₁ a₂ b₂ : ℕ}
    (h : b₂ < b₁ ∨ (b₂ = b₁ ∧ a₁ < a₂)) :
    Tendsto (fun t : ℝ => polyJetShape σ a₁ 0 b₁ t / polyJetShape σ a₂ 0 b₂ t)
      atTop (nhds 0) := by
  rcases h with hdeg | ⟨hdeg, hlog⟩
  · exact tendsto_polyJetShape_ratio_zero_of_deg hσ (by omega)
  · exact tendsto_polyJetShape_ratio_zero_of_log hσ (by omega) hlog

/-- **The dominant index of a finite family with distinct log-degrees.**  Minimizing the pair
`(b, −a)` lexicographically selects a member to which every other one is subordinate. -/
theorem exists_dominant_pair_index {N : ℕ} (hN : 0 < N) (a b : Fin N → ℕ)
    (ha : Function.Injective a) :
    ∃ β : Fin N, ∀ α : Fin N, α ≠ β → (b β < b α ∨ (b β = b α ∧ a α < a β)) := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  set M : ℕ := Finset.univ.sup a with hM
  have hle : ∀ α : Fin N, a α ≤ M := fun α => Finset.le_sup (Finset.mem_univ α)
  obtain ⟨β, -, hβ⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N))
    (fun α => toLex (b α, M - a α)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  refine ⟨β, fun α hα => ?_⟩
  have hkey := hβ α (Finset.mem_univ α)
  rw [Prod.Lex.le_iff] at hkey
  simp only [ofLex_toLex] at hkey
  rcases hkey with hlt | ⟨heq, hsnd⟩
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hane : a α ≠ a β := fun h => hα (ha h)
    have hleα := hle α
    have hleβ := hle β
    omega

/-- **The datum of a family of groups with distinct log-degrees.**  A finite sum of functions, each
with a nonzero residue against its own shape `L^{a}/s^{b}` and with the log-degrees pairwise
distinct, has the residue of its dominant member — no cancellation is possible. -/
theorem exists_dominant_shape_residue {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℂ) (a b : Fin N → ℕ) (c : Fin N → ℂ) (ha : Function.Injective a)
    (hres : ∀ α : Fin N,
      Tendsto (fun t : ℝ => F α t / polyJetShape σ (a α) 0 (b α) t) atTop (nhds (c α))) :
    ∃ β : Fin N, Tendsto (fun t : ℝ =>
      (∑ α : Fin N, F α t) / polyJetShape σ (a β) 0 (b β) t) atTop (nhds (c β)) := by
  obtain ⟨β, hβ⟩ := exists_dominant_pair_index hN a b ha
  refine ⟨β, ?_⟩
  refine tendsto_sum_div_dominant F (fun α t => polyJetShape σ (a α) 0 (b α) t) β c
    (fun α => eventually_polyJetShape_ne_zero hσ (a α) 0 (b α)) hres (fun α hα => ?_)
  exact tendsto_polyJetShape_ratio_zero_of_pair hσ (hβ α hα)

end GaloisForLFunctions
