import GaloisForLFunctions.Bottcher.BottcherDetermines

open Set Metric

namespace Bottcher

/-- **Distinct parameters ⟹ the filled Julia sets differ at a point.** From the rigidity
`c_eq_of_filledJulia_eq'` (`K_{c₁}=K_{c₂} ⟹ c₁=c₂`), `c₁≠c₂` forces a point in the symmetric difference:
a `z` in one filled Julia set but not the other. This is the seed of the `K_{c₂}`-free c₁-cylinder the
disconnected deck loop needs — by symmetry of `NoRelation` we may take `z ∈ K_{c₁} ∖ K_{c₂}`. -/
theorem exists_point_filledJulia_symmDiff {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) :
    ∃ z, (z ∈ filledJulia c₁ ∧ z ∉ filledJulia c₂) ∨ (z ∈ filledJulia c₂ ∧ z ∉ filledJulia c₁) := by
  have hKne : filledJulia c₁ ≠ filledJulia c₂ := fun h => hne (c_eq_of_filledJulia_eq' h)
  by_contra hcon
  push_neg at hcon
  apply hKne
  ext z
  exact ⟨(hcon z).1, (hcon z).2⟩

/-- **A `K_{c₂}`-free ball anchored at a `K_{c₁}`-point.** From a symmetric-difference point `z₀ ∈ K_{c₁} ∖
K_{c₂}` (available when `c₁≠c₂`, up to swapping the roles), `K_{c₂}` being closed gives an open ball around
`z₀` disjoint from `K_{c₂}` — entirely in the c₂-basin, where `φ_{c₂}` is single-valued, so any loop in it
is null-homotopic in the c₂-basin (zero `φ_{c₂}`-period, L1). Meanwhile `z₀ ∈ K_{c₁} = J_{c₁}` (dendrite/
Cantor, empty interior) so c₁-cylinders accumulate at `z₀`: the loop around such a cylinder scales
`φ_{c₁}` while fixing `φ_{c₂}` — the `σ_F` data of `q62_disconnected_both`. -/
theorem exists_ball_filledJulia_one_not_other {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) :
    ∃ (z₀ : ℂ) (r : ℝ), 0 < r ∧
      ((z₀ ∈ filledJulia c₁ ∧ Metric.ball z₀ r ∩ filledJulia c₂ = ∅) ∨
       (z₀ ∈ filledJulia c₂ ∧ Metric.ball z₀ r ∩ filledJulia c₁ = ∅)) := by
  obtain ⟨z₀, h⟩ := exists_point_filledJulia_symmDiff hne
  rcases h with ⟨hz1, hz2⟩ | ⟨hz2, hz1⟩
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl z₀ hz2
    refine ⟨z₀, r, hr, Or.inl ⟨hz1, ?_⟩⟩
    ext w
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hw1 hw2 => hsub hw1 hw2
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₁).isOpen_compl z₀ hz1
    refine ⟨z₀, r, hr, Or.inr ⟨hz2, ?_⟩⟩
    ext w
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hw1 hw2 => hsub hw1 hw2

end Bottcher

namespace Bottcher

open Set Metric

/-- **A `K_c`-free ball around the escaping critical point.** For disconnected `c` (`0 ∉ K_c`), the
critical point `0` has an open ball around it disjoint from `K_c` (`K_c` is closed). On this ball
`φ_c` is single-valued — the local chart at the figure-eight saddle (`fderiv_greenLimit_critical`,
`exists_holomorphic_completion_critical`) from which the disconnected cover is read off. -/
theorem exists_ball_zero_filledJulia_free {c : ℂ} (hc : Disconnected c) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ∩ filledJulia c = ∅ := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c).isOpen_compl 0 h0
  refine ⟨r, hr, ?_⟩
  ext w
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hw1 hw2 => hsub hw1 hw2

/-- **The common `K_{c₁} ∪ K_{c₂}`-free ball around `0`.** For `c₁, c₂` both disconnected, the common
escaping critical point `0` has a single ball around it free of BOTH filled Julia sets. This is the
base chart on which `φ_{c₁}` and `φ_{c₂}` are simultaneously single-valued: the common anchor of the
two-cylinder disconnected cover. Each `Disconnected cᵢ` puts `0` at the figure-eight saddle of `G_{cᵢ}`
(`fderiv_greenLimit_critical`); the two saddles share the point `0` but their descending Cantor lobes
(`exists_two_lobe_points`) belong to the distinct sets `K_{c₁} ≠ K_{c₂}`, so the two cylinder windings
are independent — `g_F` winds the `c₁`-lobe (scales `φ_{c₁}`, fixes `φ_{c₂}` by L1) and `g_G` winds the
`c₂`-lobe (scales `φ_{c₂}`). -/
theorem exists_ball_zero_both_free {c₁ c₂ : ℂ} (hc₁ : Disconnected c₁) (hc₂ : Disconnected c₂) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ∩ filledJulia c₁ = ∅
      ∧ Metric.ball (0 : ℂ) r ∩ filledJulia c₂ = ∅ := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_ball_zero_filledJulia_free hc₁
  obtain ⟨r₂, hr₂, h₂⟩ := exists_ball_zero_filledJulia_free hc₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, ?_⟩
  · have hsub : Metric.ball (0:ℂ) (min r₁ r₂) ∩ filledJulia c₁
        ⊆ Metric.ball (0:ℂ) r₁ ∩ filledJulia c₁ :=
      Set.inter_subset_inter_left _ (Metric.ball_subset_ball (min_le_left r₁ r₂))
    rw [h₁] at hsub; exact Set.subset_empty_iff.mp hsub
  · have hsub : Metric.ball (0:ℂ) (min r₁ r₂) ∩ filledJulia c₂
        ⊆ Metric.ball (0:ℂ) r₂ ∩ filledJulia c₂ :=
      Set.inter_subset_inter_left _ (Metric.ball_subset_ball (min_le_right r₁ r₂))
    rw [h₂] at hsub; exact Set.subset_empty_iff.mp hsub

end Bottcher
