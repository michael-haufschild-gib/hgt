/-
# One Julia set meets the other's basin (datum (d) of the repelling-cycle input)

The repelling-route obstruction `RelativeBranchFamily.false_of_repelling_branch_analytic` needs its
repelling point `z₀ ∈ J_{c₁}` to lie **off** `filledJulia c₂` — there `φ_{c₂}`, and hence the continued
relation coefficients `(Qᵢ)(·, φ_{c₂})`, are analytic. This file proves the geometric prerequisite: for
distinct parameters one of the Julia sets meets the other's basin of infinity.

From `JuliaSeparation.exists_point_filledJulia_symmDiff` (`c₁≠c₂ ⟹` a point in `K_{c₁} △ K_{c₂}`) plus a
far-field point lying in both basins, the *other* parameter's basin `Ω = Kᶜ` — preconnected
(`isPreconnected_compl_filledJulia`) — cannot avoid the frontier `∂K`: otherwise it would split between the
two disjoint opens `interior K` and `Kᶜ`, each of which it meets. So `Ω` crosses `J = ∂K`, giving a point
on `J_{c₁}` (or `J_{c₂}`) outside the other filled Julia set.
-/
import GaloisForLFunctions.Bottcher.JuliaSeparation
import GaloisForLFunctions.Bottcher.GlobalBasinBranch
import GaloisForLFunctions.Bottcher.BasinConnected

open Filter Topology Set Metric

namespace Bottcher

/-- From a point `z₀ ∈ K_a ∖ K_b`, there is a frontier point of `K_a` outside `K_b`. If `z₀` is already on
`∂K_a`, take it; otherwise `z₀ ∈ interior K_a`, and the preconnected basin `Ω_b = (K_b)ᶜ` (which contains
`z₀` and a far-field point of `Ω_a`) must cross `∂K_a`. -/
theorem exists_frontier_off {a b : ℂ} {z₀ : ℂ}
    (hz1 : z₀ ∈ filledJulia a) (hz2 : z₀ ∉ filledJulia b) :
    ∃ p, p ∈ frontier (filledJulia a) ∧ p ∉ filledJulia b := by
  by_cases hzint : z₀ ∈ interior (filledJulia a)
  · set R : ℝ := max (max 2 ‖a‖) (max 2 ‖b‖) + 1 with hRdef
    have hmnn : (0 : ℝ) ≤ max (max 2 ‖a‖) (max 2 ‖b‖) :=
      le_trans (le_trans (by norm_num) (le_max_left 2 ‖a‖)) (le_max_left _ _)
    have hRpos : 0 < R := by rw [hRdef]; linarith
    set w : ℂ := (R : ℂ) with hwdef
    have hwnorm : ‖w‖ = R := by rw [hwdef, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
    have hwa : w ∈ (filledJulia a)ᶜ := by
      apply escapeOpen_subset_compl_filledJulia a
      show max 2 ‖a‖ < ‖w‖
      rw [hwnorm, hRdef]; have := le_max_left (max 2 ‖a‖) (max 2 ‖b‖); linarith
    have hwb : w ∈ (filledJulia b)ᶜ := by
      apply escapeOpen_subset_compl_filledJulia b
      show max 2 ‖b‖ < ‖w‖
      rw [hwnorm, hRdef]; have := le_max_right (max 2 ‖a‖) (max 2 ‖b‖); linarith
    by_contra hcon
    push Not at hcon
    have hΩ₂pre : IsPreconnected ((filledJulia b)ᶜ) := isPreconnected_compl_filledJulia b
    have hfront : frontier (filledJulia a) = filledJulia a \ interior (filledJulia a) :=
      (isClosed_filledJulia a).frontier_eq
    have hcover : (filledJulia b)ᶜ ⊆ interior (filledJulia a) ∪ (filledJulia a)ᶜ := by
      intro x hx
      by_cases hxK : x ∈ filledJulia a
      · by_cases hxint : x ∈ interior (filledJulia a)
        · exact Or.inl hxint
        · exact absurd (hcon x (by rw [hfront]; exact ⟨hxK, hxint⟩)) hx
      · exact Or.inr hxK
    have hdisj : Disjoint (interior (filledJulia a)) ((filledJulia a)ᶜ) :=
      disjoint_compl_right_iff_subset.mpr interior_subset
    rcases hΩ₂pre.subset_or_subset isOpen_interior (isClosed_filledJulia a).isOpen_compl
        hdisj hcover with hsub | hsub
    · exact hwa (interior_subset (hsub hwb))
    · exact (hsub hz2) hz1
  · exact ⟨z₀, by rw [(isClosed_filledJulia a).frontier_eq]; exact ⟨hz1, hzint⟩, hz2⟩

/-- **Distinct parameters: one Julia set meets the other's basin.** For `c₁ ≠ c₂` there is a point on
`J_{c₁} = ∂K_{c₁}` outside `K_{c₂}` (or symmetrically). The geometric core of datum (d): the repelling-cycle
point `z₀ ∈ J_{c₁}` consumed by `false_of_repelling_branch_analytic` must lie off `filledJulia c₂`, where
`φ_{c₂}` — hence the continued relation coefficients — is analytic. (By `NoRelation`'s symmetry the two
disjuncts are interchangeable; the obstruction is applied to whichever Julia set is met.) -/
theorem exists_frontier_filledJulia_off_other {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) :
    (∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂) ∨
    (∃ p, p ∈ frontier (filledJulia c₂) ∧ p ∉ filledJulia c₁) := by
  obtain ⟨z₀, h⟩ := exists_point_filledJulia_symmDiff hne
  rcases h with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · exact Or.inl (exists_frontier_off h1 h2)
  · exact Or.inr (exists_frontier_off h2 h1)

/-- From a point `z₀ ∈ K_a ∖ K_b`, produce the off-other frontier point together with the two local
basin facts the natural-boundary/common-basin route consumes: a ball around the frontier point that stays
in the `b`-basin, and a nontrivial `a`-basin-side neighbourhood filter at the frontier point. -/
theorem exists_frontier_off_with_other_basin_ball {a b : ℂ} {z₀ : ℂ}
    (hz1 : z₀ ∈ filledJulia a) (hz2 : z₀ ∉ filledJulia b) :
    ∃ (p : ℂ) (r : ℝ),
      p ∈ frontier (filledJulia a) ∧
      p ∈ (filledJulia b)ᶜ ∧
      0 < r ∧
      Metric.ball p r ⊆ (filledJulia b)ᶜ ∧
      (𝓝[(filledJulia a)ᶜ] p).NeBot := by
  obtain ⟨p, hpfront, hpoff⟩ := exists_frontier_off hz1 hz2
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia b).isOpen_compl p hpoff
  have hpcl : p ∈ closure (filledJulia a)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hpfront
    exact hpfront.2
  exact ⟨p, r, hpfront, hpoff, hr, hball, mem_closure_iff_nhdsWithin_neBot.mp hpcl⟩

/-- **Distinct parameters with local basin seed data.** For `c₁ ≠ c₂`, one Julia frontier meets the
other parameter's basin, and the chosen point comes with a basin ball for the other parameter plus a
nontrivial basin-side neighbourhood filter for the frontier parameter. This is the reusable geometric
seed before any countable-avoidance or common-component strengthening. -/
theorem exists_frontier_filledJulia_off_other_with_basin_ball {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) :
    (∃ (p : ℂ) (r : ℝ),
      p ∈ frontier (filledJulia c₁) ∧
      p ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧
      Metric.ball p r ⊆ (filledJulia c₂)ᶜ ∧
      (𝓝[(filledJulia c₁)ᶜ] p).NeBot) ∨
    (∃ (p : ℂ) (r : ℝ),
      p ∈ frontier (filledJulia c₂) ∧
      p ∈ (filledJulia c₁)ᶜ ∧
      0 < r ∧
      Metric.ball p r ⊆ (filledJulia c₁)ᶜ ∧
      (𝓝[(filledJulia c₂)ᶜ] p).NeBot) := by
  obtain ⟨z₀, h⟩ := exists_point_filledJulia_symmDiff hne
  rcases h with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · exact Or.inl (exists_frontier_off_with_other_basin_ball h1 h2)
  · exact Or.inr (exists_frontier_off_with_other_basin_ball h2 h1)

end Bottcher
