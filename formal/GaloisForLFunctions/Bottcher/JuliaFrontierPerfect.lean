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

/-- Every small ball around a point of a perfect set contains uncountably many points of that set. -/
theorem not_countable_ball_inter_perfect {S : Set ℂ} (hS : Perfect S)
    {p : ℂ} (hp : p ∈ S) {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ S).Countable := by
  classical
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρlt : ρ < r := by rw [hρ]; linarith
  let D : Set ℂ := closure (Metric.ball p ρ ∩ S)
  have hD : Perfect D ∧ D.Nonempty := by
    simpa [D] using hS.closure_nhds_inter p hp (Metric.mem_ball_self hρpos) Metric.isOpen_ball
  obtain ⟨f, hfrange, _hfcont, hfinj⟩ := hD.1.exists_nat_bool_injection hD.2
  apply not_countable_of_nat_bool_injection (f := f)
  · intro y hy
    have hyD : y ∈ D := hfrange hy
    constructor
    · have hyclball : y ∈ closure (Metric.ball p ρ) := closure_mono inter_subset_left hyD
      have hyclosed : y ∈ Metric.closedBall p ρ := Metric.closure_ball_subset_closedBall hyclball
      exact Metric.closedBall_subset_ball hρlt hyclosed
    · have hyS : y ∈ S := by
        have hyclS : y ∈ closure S := closure_mono inter_subset_right hyD
        rwa [hS.closed.closure_eq] at hyclS
      exact hyS
  · exact hfinj

/-- A perfect frontier remains uncountable in every open region that meets it. -/
theorem not_countable_frontier_inter_open_of_perfect_frontier {K Ω : Set ℂ}
    (hfront : Perfect (frontier K)) (hΩopen : IsOpen Ω)
    {p : ℂ} (hpfront : p ∈ frontier K) (hpΩ : p ∈ Ω) :
    ¬ ((frontier K ∩ Ω).Countable) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩopen p hpΩ
  have hunc : ¬ (Metric.ball p r ∩ frontier K).Countable :=
    not_countable_ball_inter_perfect hfront hpfront hr
  intro hcount
  apply hunc
  apply hcount.mono
  intro z hz
  exact ⟨hz.2, hball hz.1⟩

/-- Countable-deletion form for a perfect frontier in an open region. -/
theorem countableAvoidance_frontier_open_of_perfect_frontier {K Ω : Set ℂ}
    (hfront : Perfect (frontier K)) (hΩopen : IsOpen Ω)
    {p : ℂ} (hpfront : p ∈ frontier K) (hpΩ : p ∈ Ω) :
    ∀ T : Set ℂ, T.Countable → ∃ z₀, z₀ ∈ frontier K ∧ z₀ ∈ Ω ∧ z₀ ∉ T := by
  intro T hT
  by_contra hnone
  have hsub : frontier K ∩ Ω ⊆ T := by
    intro z hz
    by_contra hzT
    exact hnone ⟨z, hz.1, hz.2, hzT⟩
  exact not_countable_frontier_inter_open_of_perfect_frontier hfront hΩopen hpfront hpΩ (hT.mono hsub)

/-- Countable-deletion form for a perfect frontier in the complement of a closed set. -/
theorem countableAvoidance_frontier_off_closed_of_perfect_frontier {K₁ K₂ : Set ℂ}
    (hfront : Perfect (frontier K₁)) (hK₂closed : IsClosed K₂)
    {p : ℂ} (hpfront : p ∈ frontier K₁) (hpK₂ : p ∉ K₂) :
    ∀ T : Set ℂ, T.Countable → ∃ z₀, z₀ ∈ frontier K₁ ∧ z₀ ∉ K₂ ∧ z₀ ∉ T := by
  intro T hT
  obtain ⟨z₀, hzfront, hzoff, hzT⟩ :=
    countableAvoidance_frontier_open_of_perfect_frontier hfront hK₂closed.isOpen_compl hpfront hpK₂ T hT
  exact ⟨z₀, hzfront, hzoff, hzT⟩

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

/-- Interior-region form of
`not_countable_frontier_inter_open_inter_other_basin_of_perfect_emptyInterior`.  The analytic region
need not be globally open; it is enough that the seed point lies in its interior. -/
theorem not_countable_frontier_inter_region_other_basin_of_perfect_emptyInterior
    {c₁ c₂ : ℂ} {Ω : Set ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rOther : ℝ} (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ¬ (((frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable) := by
  have huncInterior :
      ¬ (((frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ) ∩ interior Ω).Countable) :=
    not_countable_frontier_inter_open_inter_other_basin_of_perfect_emptyInterior
      hK hempty isOpen_interior hpK hpΩ hrOther hother
  intro hcount
  apply huncInterior
  apply hcount.mono
  intro z hz
  exact ⟨hz.1, interior_subset hz.2⟩

/-- Countable-deletion form for an arbitrary analytic region with the seed point in its interior. -/
theorem countableAvoidance_frontier_region_other_basin_of_perfect_emptyInterior
    {c₁ c₂ : ℂ} {Ω : Set ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rOther : ℝ} (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∀ T : Set ℂ, T.Countable →
      ∃ z₀ ∈ frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ, z₀ ∈ Ω ∧ z₀ ∉ T := by
  intro T hT
  by_contra hnone
  push Not at hnone
  have hsub : ((frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ) ∩ Ω) ⊆ T := by
    intro z hz
    exact hnone z hz.1 hz.2
  exact not_countable_frontier_inter_region_other_basin_of_perfect_emptyInterior
      hK hempty hpK hpΩ hrOther hother (hT.mono hsub)

/-- A local basin sector forces nearby frontier points into the closure of the sector carrier. -/
theorem frontier_mem_closure_of_basin_sector {K U : Set ℂ} {p z : ℂ} {r : ℝ}
    (hzball : z ∈ Metric.ball p r) (hzfront : z ∈ frontier K)
    (hsector : Metric.ball p r ∩ Kᶜ ⊆ U) :
    z ∈ closure U := by
  have hzcl : z ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hzfront
    exact hzfront.2
  rw [_root_.mem_closure_iff]
  intro W hWo hzW
  have hmeet := (_root_.mem_closure_iff.mp hzcl) (W ∩ Metric.ball p r)
    (hWo.inter Metric.isOpen_ball) ⟨hzW, hzball⟩
  rcases hmeet with ⟨y, ⟨hyW, hyball⟩, hyKc⟩
  exact ⟨y, hyW, hsector ⟨hyball, hyKc⟩⟩

/-- Local target-set uncountability: after shrinking inside a prescribed local sector radius, there are
still uncountably many frontier/off-other points in the analytic region. -/
theorem not_countable_local_frontier_inter_region_other_basin_of_perfect_emptyInterior
    {c₁ c₂ : ℂ} {Ω : Set ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rLocal rOther : ℝ} (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable) := by
  obtain ⟨rΩ, hrΩ, hballΩ⟩ := Metric.isOpen_iff.mp isOpen_interior p hpΩ
  set r : ℝ := min (min rLocal rOther) rΩ with hrdef
  have hr : 0 < r := by rw [hrdef]; exact lt_min (lt_min hrLocal hrOther) hrΩ
  have hunc : ¬ (Metric.ball p r ∩ frontier (filledJulia c₁)).Countable :=
    not_countable_ball_inter_frontier_of_perfect_emptyInterior hK hempty hpK hr
  intro hcount
  apply hunc
  apply hcount.mono
  intro z hz
  rcases hz with ⟨hzball, hzfront⟩
  have hzLocal : z ∈ Metric.ball p rLocal :=
    Metric.ball_subset_ball
      (by rw [hrdef]; exact (min_le_left (min rLocal rOther) rΩ).trans (min_le_left rLocal rOther))
      hzball
  have hzOther : z ∈ (filledJulia c₂)ᶜ :=
    hother (Metric.ball_subset_ball
      (by rw [hrdef]; exact (min_le_left (min rLocal rOther) rΩ).trans (min_le_right rLocal rOther))
      hzball)
  have hzΩ : z ∈ Ω :=
    interior_subset (hballΩ (Metric.ball_subset_ball (by rw [hrdef]; exact min_le_right (min rLocal rOther) rΩ) hzball))
  exact ⟨⟨⟨hzLocal, hzfront⟩, hzOther⟩, hzΩ⟩

/-- Local target-set package for the empty-interior common-basin route.  A perfect empty-interior
filled Julia set supplies a target set with countable avoidance; a local basin-sector inclusion supplies
the closure-against-`U` condition for all those targets. -/
theorem exists_local_frontier_target_set_countableAvoidance_closure_of_perfect_emptyInterior
    {U Ω : Set ℂ} {c₁ c₂ : ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rLocal rOther : ℝ} (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S, z₀ ∈ filledJulia c₁ ∧ z₀ ∈ (filledJulia c₂)ᶜ) := by
  let S : Set ℂ := (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ
  refine ⟨S, ?_, ?_, ?_⟩
  · intro T hT
    by_contra hnone
    push Not at hnone
    have hsub : (S ∩ Ω) ⊆ T := by
      intro z hz
      exact hnone z hz.1 hz.2
    have hunc : ¬ (S ∩ Ω).Countable := by
      simpa [S] using not_countable_local_frontier_inter_region_other_basin_of_perfect_emptyInterior
        hK hempty hpK hpΩ hrLocal hrOther hother
    exact hunc (hT.mono hsub)
  · intro z hzS
    exact frontier_mem_closure_of_basin_sector hzS.1.1 hzS.1.2 hsector
  · intro z hzS
    exact ⟨mem_filledJulia_of_frontier hzS.1.2, hzS.2⟩

/-- Stronger local target-set package retaining the concrete local frontier description.  This is the
form consumed by the countable-avoidance hRigid endpoint: the target set avoids every countable bad set,
lies in `closure U`, and every target point is still known to be in the prescribed local frontier/off-other
slice. -/
theorem exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_perfect_emptyInterior
    {U Ω : Set ℂ} {c₁ c₂ : ℂ} (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rLocal rOther : ℝ} (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ Metric.ball p rLocal ∧ z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ) := by
  let S : Set ℂ := (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ
  refine ⟨S, ?_, ?_, ?_⟩
  · intro T hT
    by_contra hnone
    push Not at hnone
    have hsub : (S ∩ Ω) ⊆ T := by
      intro z hz
      exact hnone z hz.1 hz.2
    have hunc : ¬ (S ∩ Ω).Countable := by
      simpa [S] using not_countable_local_frontier_inter_region_other_basin_of_perfect_emptyInterior
        hK hempty hpK hpΩ hrLocal hrOther hother
    exact hunc (hT.mono hsub)
  · intro z hzS
    exact frontier_mem_closure_of_basin_sector hzS.1.1 hzS.1.2 hsector
  · intro z hzS
    exact ⟨hzS.1.1, hzS.1.2, hzS.2⟩

/-- Generic good-local-frontier target selector.  If uncountably many local frontier/off-other points
in the analytic region satisfy a predicate `G`, then countable avoidance can be performed inside that
good set, while the local basin-sector inclusion still supplies carrier closure. -/
theorem exists_local_frontier_good_target_set_countableAvoidance_closure_frontier
    {U Ω G : Set ℂ} {c₁ c₂ p : ℂ} {rLocal : ℝ}
    (hunc :
      ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ G) ∩ Ω).Countable))
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ Metric.ball p rLocal ∧ z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∈ G) := by
  let S : Set ℂ := ((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ G
  refine ⟨S, ?_, ?_, ?_⟩
  · intro T hT
    by_contra hnone
    push Not at hnone
    have hsub : (S ∩ Ω) ⊆ T := by
      intro z hz
      exact hnone z hz.1 hz.2
    exact hunc (hT.mono hsub)
  · intro z hzS
    exact frontier_mem_closure_of_basin_sector hzS.1.1.1 hzS.1.1.2 hsector
  · intro z hzS
    exact ⟨hzS.1.1.1, hzS.1.1.2, hzS.1.2, hzS.2⟩

/-- Slit-good local-frontier target selector.  The remaining geometric input is now exactly
uncountability of local frontier/off-other points whose translated slit sector lies in the basin at
every scale.  From that, this theorem builds the target set needed by the countable-avoidance hRigid
route. -/
theorem exists_local_frontier_slit_target_set_countableAvoidance_closure_frontier
    {U Ω : Set ℂ} {c₁ c₂ p : ℂ} {rLocal : ℝ}
    (hunc :
      ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
        {z₀ : ℂ | ∀ ρ, 0 < ρ →
          Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable))
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ Metric.ball p rLocal ∧ z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          (∀ ρ, 0 < ρ →
            Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  exact exists_local_frontier_good_target_set_countableAvoidance_closure_frontier
    (G := {z₀ : ℂ | ∀ ρ, 0 < ρ →
      Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
        Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) hunc hsector

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

theorem filledJulia_nontrivial (c : ℂ) :
    (filledJulia c).Nontrivial := by
  obtain ⟨z, hzfix1⟩ := exists_periodic_point c 1 (by norm_num)
  have hzfix : quadratic c z = z := by simpa using hzfix1
  have hzK : z ∈ filledJulia c := mem_filledJulia_of_fixed hzfix
  by_cases hz0 : z = 0
  · have hc0 : c = 0 := by
      have hfix0 : quadratic c 0 = 0 := by simpa [hz0] using hzfix
      simpa [quadratic] using hfix0
    refine ⟨0, ?_, 1, ?_, ?_⟩
    · simpa [hz0] using hzK
    · have h1fix : quadratic c 1 = 1 := by
        rw [hc0]
        norm_num [quadratic]
      exact mem_filledJulia_of_fixed h1fix
    · norm_num
  · have hnegK : -z ∈ filledJulia c := by
      apply (mem_filledJulia_iff_quadratic_mem c (-z)).mpr
      have hzsq : z ^ 2 + c = z := by simpa [quadratic_apply] using hzfix
      simpa [quadratic_apply, hzsq] using hzK
    refine ⟨z, hzK, -z, hnegK, ?_⟩
    intro h
    apply hz0
    have hsum : z + z = 0 := by
      have h' : z + z = -z + z := congrArg (fun t : ℂ => t + z) h
      calc
        z + z = -z + z := h'
        _ = 0 := by ring
    have htwoz : (2 : ℂ) * z = 0 := by
      calc
        (2 : ℂ) * z = z + z := by ring
        _ = 0 := hsum
    exact (mul_eq_zero.mp htwoz).resolve_left (by norm_num)

theorem filledJulia_nontrivial_of_ne_quarter {c : ℂ} (_hc : c ≠ 1 / 4) :
    (filledJulia c).Nontrivial := by
  exact filledJulia_nontrivial c

theorem not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior
    {c p : ℂ} (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅) (hp : p ∈ filledJulia c)
    {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier (filledJulia c)).Countable :=
  not_countable_ball_inter_frontier_filledJulia_of_perfect_emptyInterior
    (perfect_filledJulia_of_preconnected_nontrivial hconn (filledJulia_nontrivial c))
    hempty hp hr

theorem not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior_ne_quarter
    {c p : ℂ} (_hc : c ≠ 1 / 4) (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅) (hp : p ∈ filledJulia c)
    {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier (filledJulia c)).Countable :=
  not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior hconn hempty hp hr

/-- Connected filled Julia sets supply the local target-set package without a separate `Perfect`
hypothesis. This is the form needed by the connected hRigid lane: countable avoidance, closure against
the carrier `U`, and the concrete local frontier/off-other description all come from connectedness,
global nontriviality of `K_c`, empty interior, and the local sector/off-other balls. -/
theorem exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
    {U Ω : Set ℂ} {c₁ c₂ : ℂ} (hconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rLocal rOther : ℝ} (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ Metric.ball p rLocal ∧ z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ) := by
  exact exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_perfect_emptyInterior
    (perfect_filledJulia_of_preconnected_nontrivial hconn (filledJulia_nontrivial c₁))
    hempty hpK hpΩ hrLocal hrOther hsector hother

theorem exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior_ne_quarter
    {U Ω : Set ℂ} {c₁ c₂ : ℂ} (_hc₁ : c₁ ≠ 1 / 4)
    (hconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rLocal rOther : ℝ} (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ Metric.ball p rLocal ∧ z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ) := by
  exact exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
    hconn hempty hpK hpΩ hrLocal hrOther hsector hother

end Bottcher
