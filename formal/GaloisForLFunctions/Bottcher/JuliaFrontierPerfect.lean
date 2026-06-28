import GaloisForLFunctions.Bottcher.DendriteContinuesAcross
import GaloisForLFunctions.Bottcher.PeriodicPoints
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Data.Set.Countable

open Complex Metric Topology Set Filter

namespace Bottcher

private theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  classical
  intro h
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (ℕ → Bool)
  apply Function.cantor_injective (fun S : Set ℕ => g (fun n => if n ∈ S then true else false))
  intro A B hAB
  apply hg at hAB
  ext n
  have hfun := congrFun hAB n
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [hA, hB] at hfun ⊢

private theorem not_countable_of_nat_bool_injection {s : Set ℂ}
    {f : (ℕ → Bool) → ℂ} (hfs : Set.range f ⊆ s) (hfinj : Function.Injective f) :
    ¬ s.Countable := by
  intro hs
  haveI : Countable s := hs.to_subtype
  let F : (ℕ → Bool) → s := fun x => ⟨f x, hfs (Set.mem_range_self x)⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply hfinj
    exact Subtype.ext_iff.mp hxy
  exact not_countable_nat_bool hF.countable

/-- In a perfect closed set with empty interior, every small ball around a point of the set contains
uncountably many frontier points. -/
theorem not_countable_ball_inter_frontier_of_perfect_emptyInterior
    {K : Set ℂ} (hK : Perfect K) (hempty : interior K = ∅)
    {p : ℂ} (hp : p ∈ K) {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier K).Countable := by
  classical
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρlt : ρ < r := by rw [hρ]; linarith
  let D : Set ℂ := closure (Metric.ball p ρ ∩ K)
  have hD : Perfect D ∧ D.Nonempty := by
    simpa [D] using hK.closure_nhds_inter p hp (Metric.mem_ball_self hρpos) Metric.isOpen_ball
  obtain ⟨f, hfrange, _hfcont, hfinj⟩ := hD.1.exists_nat_bool_injection hD.2
  apply not_countable_of_nat_bool_injection (f := f)
  · intro y hy
    have hyD : y ∈ D := hfrange hy
    constructor
    · have hyclball : y ∈ closure (Metric.ball p ρ) := closure_mono inter_subset_left hyD
      have hyclosed : y ∈ Metric.closedBall p ρ := Metric.closure_ball_subset_closedBall hyclball
      exact Metric.closedBall_subset_ball hρlt hyclosed
    · have hyK : y ∈ K := by
        have hyclK : y ∈ closure K := closure_mono inter_subset_right hyD
        rwa [hK.closed.closure_eq] at hyclK
      rw [hK.closed.frontier_eq]
      exact ⟨hyK, by simp [hempty]⟩
  · exact hfinj

/-- Open-region form: after shrinking inside an open analytic region, the frontier supply remains
uncountable. -/
theorem exists_uncountable_frontier_ball_subset_open_of_perfect_emptyInterior
    {K Ω : Set ℂ} (hK : Perfect K) (hempty : interior K = ∅)
    (hΩopen : IsOpen Ω) {p : ℂ} (hpK : p ∈ K) (hpΩ : p ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ Ω ∧
      ¬ (Metric.ball p r ∩ frontier K).Countable := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩopen p hpΩ
  exact ⟨r, hr, hball, not_countable_ball_inter_frontier_of_perfect_emptyInterior hK hempty hpK hr⟩

/-- The common-basin target set supplied by a perfect empty-interior filled Julia set is uncountable
inside any open analytic region and any available off-other basin ball. -/
theorem not_countable_frontier_inter_open_inter_other_basin_of_perfect_emptyInterior
    {c₁ c₂ : ℂ} {Ω : Set ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅) (hΩopen : IsOpen Ω)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ Ω)
    {rOther : ℝ} (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ¬ (((frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable) := by
  obtain ⟨rΩ, hrΩ, hballΩ⟩ := Metric.isOpen_iff.mp hΩopen p hpΩ
  set r : ℝ := min rΩ rOther with hrdef
  have hr : 0 < r := by rw [hrdef]; exact lt_min hrΩ hrOther
  have hunc : ¬ (Metric.ball p r ∩ frontier (filledJulia c₁)).Countable :=
    not_countable_ball_inter_frontier_of_perfect_emptyInterior hK hempty hpK hr
  intro hcount
  apply hunc
  apply hcount.mono
  intro z hz
  rcases hz with ⟨hzball, hzfront⟩
  exact ⟨⟨hzfront, hother (Metric.ball_subset_ball (by rw [hrdef]; exact min_le_right _ _) hzball)⟩,
    hballΩ (Metric.ball_subset_ball (by rw [hrdef]; exact min_le_left _ _) hzball)⟩

/-- Countable-deletion form: the target frontier point can be chosen in the analytic region, in the
other basin, and outside any prescribed countable exceptional set. -/
theorem countableAvoidance_frontier_open_other_basin_of_perfect_emptyInterior
    {c₁ c₂ : ℂ} {Ω : Set ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅) (hΩopen : IsOpen Ω)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ Ω)
    {rOther : ℝ} (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∀ T : Set ℂ, T.Countable →
      ∃ z₀, z₀ ∈ frontier (filledJulia c₁) ∧ z₀ ∈ Ω ∧ z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T := by
  intro T hT
  by_contra hnone
  push Not at hnone
  have hsub : ((frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ) ∩ Ω) ⊆ T := by
    intro z hz
    exact hnone z hz.1.1 hz.2 hz.1.2
  exact not_countable_frontier_inter_open_inter_other_basin_of_perfect_emptyInterior
      hK hempty hΩopen hpK hpΩ hrOther hother (hT.mono hsub)

theorem not_countable_ball_inter_frontier_filledJulia_of_perfect_emptyInterior
    {c p : ℂ} (hK : Perfect (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hp : p ∈ filledJulia c) {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier (filledJulia c)).Countable :=
  not_countable_ball_inter_frontier_of_perfect_emptyInterior hK hempty hp hr

theorem perfect_filledJulia_of_preconnected_nontrivial {c : ℂ}
    (hconn : IsPreconnected (filledJulia c)) (hnon : (filledJulia c).Nontrivial) :
    Perfect (filledJulia c) := by
  exact ⟨isClosed_filledJulia c, hconn.preperfect_of_nontrivial hnon⟩

theorem filledJulia_nontrivial_of_ne_quarter {c : ℂ} (hc : c ≠ 1 / 4) :
    (filledJulia c).Nontrivial := by
  obtain ⟨α, β, hα, hβ, hne⟩ := exists_two_distinct_fixed_points c hc
  exact ⟨α, mem_filledJulia_of_fixed hα, β, mem_filledJulia_of_fixed hβ, hne⟩

theorem not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior_ne_quarter
    {c p : ℂ} (hc : c ≠ 1 / 4) (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅) (hp : p ∈ filledJulia c)
    {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier (filledJulia c)).Countable :=
  not_countable_ball_inter_frontier_filledJulia_of_perfect_emptyInterior
    (perfect_filledJulia_of_preconnected_nontrivial hconn (filledJulia_nontrivial_of_ne_quarter hc))
    hempty hp hr

end Bottcher
