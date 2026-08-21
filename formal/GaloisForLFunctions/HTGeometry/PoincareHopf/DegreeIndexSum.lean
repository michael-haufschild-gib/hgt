import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeAdditivity

/-!
# The degree is the sum of the local indices

For a `C²` field on a bounded open set whose zeros in the closure form a finite set inside the set,
the degree at `0` is the sum of the indices at those zeros.  Small enough balls around the zeros are
pairwise disjoint, sit inside the open set, and isolate their centres, so degree additivity applies
and each piece is an index.

This is the Poincaré–Hopf statement for a flat domain; the manifold statement is assembled from it
chart by chart.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {v : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)}

/-- A finite set of points in an open set is uniformly separated and uniformly interior. -/
theorem exists_separating_radius (hΩ : IsOpen Ω) (Z : Finset (Fin n → ℝ)) (hZsub : ↑Z ⊆ Ω) :
    ∃ ε > 0, (∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → ε + ε ≤ dist p q) ∧
      ∀ p ∈ Z, Metric.closedBall p ε ⊆ Ω := by
  classical
  -- uniform interior radius
  have hrad : ∀ p ∈ Z, ∃ r > 0, Metric.closedBall p r ⊆ Ω := by
    intro p hp
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p (hZsub hp)
    exact ⟨r / 2, by linarith, fun x hx => hball (by
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith)⟩
  choose! r hrpos hrsub using hrad
  -- uniform separation
  obtain ⟨ε₁, hε₁pos, hε₁⟩ :
      ∃ ε > 0, ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → ε + ε ≤ dist p q := by
    set P := (Z ×ˢ Z).filter (fun pq => pq.1 ≠ pq.2) with hP
    rcases P.eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, fun p hp q hq hpq => ?_⟩
      exact absurd (by rw [hP]; simp [Finset.mem_filter, Finset.mem_product, hp, hq, hpq] :
        (p, q) ∈ P) (by rw [hemp]; simp)
    · obtain ⟨pq, hpq, hmin⟩ := P.exists_min_image (fun pq => dist pq.1 pq.2) hne
      have hne' : pq.1 ≠ pq.2 := by
        have := (Finset.mem_filter.mp (by rw [hP] at hpq; exact hpq)).2
        exact this
      have hdpos : 0 < dist pq.1 pq.2 := dist_pos.mpr hne'
      refine ⟨dist pq.1 pq.2 / 3, by linarith, fun p hp q hq hpq' => ?_⟩
      have hmem : (p, q) ∈ P := by
        rw [hP]; simp [Finset.mem_filter, Finset.mem_product, hp, hq, hpq']
      have := hmin (p, q) hmem
      simp only at this
      linarith
  -- uniform interior
  obtain ⟨ε₂, hε₂pos, hε₂⟩ : ∃ ε > 0, ∀ p ∈ Z, Metric.closedBall p ε ⊆ Ω := by
    rcases Z.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun p hp => absurd hp (by rw [hemp]; simp)⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := Z.exists_min_image r hne
      refine ⟨r p₀, hrpos p₀ hp₀, fun p hp => ?_⟩
      exact subset_trans (Metric.closedBall_subset_closedBall (hmin p hp)) (hrsub p hp)
  exact ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos,
    fun p hp q hq hpq => le_trans (by
      have := min_le_left ε₁ ε₂
      linarith) (hε₁ p hp q hq hpq),
    fun p hp => subset_trans (Metric.closedBall_subset_closedBall (min_le_right ε₁ ε₂))
      (hε₂ p hp)⟩

/-- **The degree is the sum of the indices at the zeros.** -/
theorem degree_eq_sum_index (hv : ContDiff ℝ 2 v) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Z : Finset (Fin n → ℝ)) (hZsub : ↑Z ⊆ Ω)
    (hZmem : ∀ x ∈ closure Ω, v x = 0 → x ∈ Z) :
    degree v Ω 0 = ∑ p ∈ Z, index v p := by
  classical
  obtain ⟨ε, hεpos, hsep, hsub⟩ := exists_separating_radius hΩ Z hZsub
  set U : {x // x ∈ Z} → Set (Fin n → ℝ) := fun p => Metric.ball (p : Fin n → ℝ) ε with hU
  have hUopen : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  have hUsub : ∀ i, U i ⊆ Ω := fun i =>
    subset_trans Metric.ball_subset_closedBall (hsub i i.2)
  have hUdisj : ∀ i j : {x // x ∈ Z}, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    refine Metric.ball_disjoint_ball ?_
    exact hsep i i.2 j j.2 (fun hcon => hij (Subtype.ext hcon))
  have hout : ∀ x ∈ closure Ω \ (⋃ i, U i), v x ≠ 0 := by
    intro x hx hvx
    have hxZ : x ∈ Z := hZmem x hx.1 hvx
    exact hx.2 (Set.mem_iUnion.mpr ⟨⟨x, hxZ⟩, Metric.mem_ball_self hεpos⟩)
  have hisol : ∀ p ∈ Z, IsolatingRadius v p ε := by
    intro p hp
    refine ⟨hεpos, fun x hx hxp hvx => ?_⟩
    have hxΩ : x ∈ Ω := hsub p hp hx
    have hxZ : x ∈ Z := hZmem x (subset_closure hxΩ) hvx
    have hd := hsep x hxZ p hp hxp
    rw [Metric.mem_closedBall] at hx
    linarith
  rw [degree_eq_sum_of_disjoint hv hΩ hΩb U hUopen hUsub hUdisj hout]
  rw [← Finset.sum_coe_sort Z (fun p => index v p)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (index_eq_degree hv (hisol i i.2)).symm

end GaloisForLFunctions.HTGeometry.PoincareHopf
