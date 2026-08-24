import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer
import GaloisForLFunctions.HTGeometry.DivisorPairing

open Complex Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped Topology

/-- Compact-open convergence of entire functions preserves complete zero divisor, with
multiplicity, in every bounded open set whose frontier is zero-free for the nonzero limit. -/
theorem eventually_exists_zeroSet_boundedOpen_of_tendstoLocallyUniformly
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hf : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformly F f atTop)
    {a₀ : ℂ} (ha₀ : f a₀ ≠ 0)
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hfrontier : ∀ z ∈ frontier Ω, f z ≠ 0) :
    ∃ A : Finset ℂ,
      (∀ z ∈ Ω, f z = 0 ↔ z ∈ A) ∧
      ∀ᶠ n : ℕ in atTop, ∃ Z : Finset ℂ,
        (∀ z ∈ Ω, F n z = 0 ↔ z ∈ Z) ∧
        (∑ z ∈ Z, zeroMult (F n) z) = ∑ a ∈ A, zeroMult f a := by
  classical
  have hΩcompact : IsCompact (closure Ω) := hΩbounded.isCompact_closure
  have hfanalytic : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hiso : ∀ z ∈ (Set.univ : Set ℂ),
      ¬ (∀ᶠ w in nhds z, f w = 0) := by
    intro z _ hzero
    have heq : Set.EqOn f 0 Set.univ :=
      hfanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hzero
    exact ha₀ (heq (Set.mem_univ a₀))
  have hAfin : (closure Ω ∩ {z | f z = 0}).Finite :=
    finite_zeros_of_isCompact isOpen_univ hf.differentiableOn hiso
      hΩcompact (by simp)
  let A : Finset ℂ := hAfin.toFinset
  have hAmem (z : ℂ) : z ∈ A ↔ z ∈ closure Ω ∧ f z = 0 := by
    simp only [A, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
  have hAΩ : ∀ a ∈ A, a ∈ Ω := by
    intro a ha
    have ha' := (hAmem a).mp ha
    rw [closure_eq_self_union_frontier] at ha'
    rcases ha'.1 with haΩ | hafrontier
    · exact haΩ
    · exact absurd ha'.2 (hfrontier a hafrontier)
  have hAzero : ∀ z ∈ Ω, f z = 0 ↔ z ∈ A := by
    intro z hzΩ
    rw [hAmem]
    exact ⟨fun hz => ⟨subset_closure hzΩ, hz⟩, fun hz => hz.2⟩

  have hradius : ∀ a : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      (a ∈ A → closedBall a ρ ⊆ Ω) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩopen a (hAΩ a ha)
      refine ⟨r / 2, by positivity, fun _ z hz => hrΩ ?_⟩
      rw [mem_ball]
      have := mem_closedBall.mp hz
      linarith
    · exact ⟨1, one_pos, fun h => absurd h ha⟩
  choose ρ hρpos hρball using hradius
  let Eρ : Finset ℝ := insert 1 (A.image ρ)
  have hEρ : Eρ.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let ρ₀ : ℝ := Eρ.min' hEρ
  have hρ₀pos : 0 < ρ₀ := by
    dsimp only [ρ₀]
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · simp [h]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hρpos a
  have hρ₀le : ∀ a ∈ A, ρ₀ ≤ ρ a := by
    intro a ha
    exact Finset.min'_le Eρ (ρ a)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ρ ha))
  obtain ⟨δ, hδ, hδρ, hsep⟩ := exists_separating_radius A hρ₀pos
  have hballΩ : ∀ a ∈ A, closedBall a (2 * δ) ⊆ Ω := by
    intro a ha z hz
    apply hρball a ha
    rw [mem_closedBall]
    have hz' := mem_closedBall.mp hz
    exact hz'.trans (by linarith [hδρ, hρ₀le a ha])
  have hsmallBallΩ : ∀ a ∈ A, ball a δ ⊆ Ω := by
    intro a ha z hz
    exact hballΩ a ha (ball_subset_closedBall (by
      rw [mem_ball] at hz ⊢
      linarith))

  have hloc : ∀ a : ℂ, ∃ ε : ℝ, 0 < ε ∧ (a ∈ A →
      ∀ h : ℂ → ℂ, Differentiable ℂ h →
        (∀ z ∈ closedBall a (2 * δ), ‖h z - f z‖ ≤ ε) →
          ∃ Za : Finset ℂ, (∀ w ∈ Za, w ∈ ball a δ) ∧
            (∀ z ∈ ball a δ, h z = 0 ↔ z ∈ Za) ∧
            (∑ w ∈ Za, zeroMult h w) = zeroMult f a) := by
    intro a
    by_cases ha : a ∈ A
    · have ha0 : f a = 0 := (hAmem a).mp ha |>.2
      have honly : ∀ w ∈ closedBall a (2 * δ), f w = 0 → w = a := by
        intro w hw hw0
        by_contra hwa
        have hwA : w ∈ A := (hAzero w (hballΩ a ha hw)).mp hw0
        have hfar := hsep a ha w hwA (Ne.symm hwa)
        have hnear := mem_closedBall.mp hw
        rw [dist_comm] at hnear
        linarith
      obtain ⟨ε, hε, hstable⟩ := exists_local_zeroSet isOpen_univ
        hf.differentiableOn hδ (by simp) ha0 honly
      exact ⟨ε, hε, fun _ h hdiff hclose =>
        hstable h hdiff.differentiableOn hclose⟩
    · exact ⟨1, one_pos, fun h => absurd h ha⟩
  choose εf hεfpos hεfprop using hloc

  let W : Set ℂ := closure Ω \ ⋃ a ∈ (A : Set ℂ), ball a δ
  have hWcompact : IsCompact W :=
    hΩcompact.diff (isOpen_biUnion fun a _ => isOpen_ball)
  have hWclosure : W ⊆ closure Ω := Set.sdiff_subset
  have hWne : ∀ z ∈ W, f z ≠ 0 := by
    intro z hz hz0
    have hzA : z ∈ (A : Set ℂ) := by
      rw [Finset.mem_coe, hAmem]
      exact ⟨hz.1, hz0⟩
    exact hz.2 (mem_biUnion hzA (mem_ball_self hδ))
  obtain ⟨c₀, hc₀pos, hc₀⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z ∈ W, c₀ ≤ ‖f z‖ := by
    rcases W.eq_empty_or_nonempty with hWe | hWn
    · exact ⟨1, one_pos, fun z hz => by simp [hWe] at hz⟩
    · obtain ⟨w, hw, hmin⟩ := hWcompact.exists_isMinOn hWn hf.continuous.continuousOn.norm
      exact ⟨‖f w‖, norm_pos_iff.mpr (hWne w hw), fun z hz => hmin hz⟩
  let E : Finset ℝ := insert (c₀ / 2) (A.image εf)
  have hE : E.Nonempty := ⟨c₀ / 2, Finset.mem_insert_self _ _⟩
  let ε : ℝ := E.min' hE
  have hεpos : 0 < ε := by
    dsimp only [ε]
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      positivity
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hεfpos a
  have hεc₀ : ε ≤ c₀ / 2 :=
    Finset.min'_le E _ (Finset.mem_insert_self _ _)
  have hεa : ∀ a ∈ A, ε ≤ εf a := by
    intro a ha
    exact Finset.min'_le E _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem εf ha))
  have hconvClosure : TendstoUniformlyOn F f atTop (closure Ω) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hΩcompact).mp
      hconv.tendstoLocallyUniformlyOn
  have hclose : ∀ᶠ n : ℕ in atTop, ∀ z ∈ closure Ω,
      ‖F n z - f z‖ ≤ ε := by
    have hlt := (Metric.tendstoUniformlyOn_iff.mp hconvClosure) ε hεpos
    filter_upwards [hlt] with n hn
    intro z hz
    have := hn z hz
    simpa only [dist_eq_norm, norm_sub_rev] using this.le
  refine ⟨A, hAzero, ?_⟩
  filter_upwards [hclose] with n hn
  have hnW : ∀ z ∈ W, F n z ≠ 0 := by
    intro z hz hz0
    have h1 := hn z (hWclosure hz)
    rw [hz0, zero_sub, norm_neg] at h1
    have h2 := hc₀ z hz
    linarith [hεc₀]
  have hlocn : ∀ a : ℂ, ∃ Za : Finset ℂ, a ∈ A →
      ((∀ w ∈ Za, w ∈ ball a δ) ∧
        (∀ z ∈ ball a δ, F n z = 0 ↔ z ∈ Za) ∧
        (∑ w ∈ Za, zeroMult (F n) w) = zeroMult f a) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨Za, hZa⟩ := hεfprop a ha (F n) (hF n) fun z hz =>
        (hn z (subset_closure (hballΩ a ha hz))).trans (hεa a ha)
      exact ⟨Za, fun _ => hZa⟩
    · exact ⟨∅, fun h => absurd h ha⟩
  choose Za hZa using hlocn
  let Z : Finset ℂ := A.biUnion Za
  have hZzero : ∀ z ∈ Ω, F n z = 0 ↔ z ∈ Z := by
    intro z hzΩ
    constructor
    · intro hz0
      have hzunion : z ∈ ⋃ a ∈ (A : Set ℂ), ball a δ := by
        by_contra hznot
        exact hnW z ⟨subset_closure hzΩ, hznot⟩ hz0
      obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hzunion
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_coe.mp ha,
        ((hZa a (Finset.mem_coe.mp ha)).2.1 z hza).mp hz0⟩
    · intro hzZ
      obtain ⟨a, ha, hza⟩ := Finset.mem_biUnion.mp hzZ
      have hball := (hZa a ha).1 z hza
      exact ((hZa a ha).2.1 z hball).mpr hza
  have hdisj : (A : Set ℂ).PairwiseDisjoint Za := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr fun z hza hzb => ?_
    have hza' := (hZa a (Finset.mem_coe.mp ha)).1 z hza
    have hzb' := (hZa b (Finset.mem_coe.mp hb)).1 z hzb
    have htri : dist a b ≤ dist a z + dist z b := dist_triangle a z b
    rw [dist_comm a z] at htri
    have hfar := hsep a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
    have haδ := mem_ball.mp hza'
    have hbδ := mem_ball.mp hzb'
    linarith
  refine ⟨Z, hZzero, ?_⟩
  dsimp only [Z]
  rw [Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl fun a ha => (hZa a ha).2.2

end GaloisForLFunctions.HTGeometry
