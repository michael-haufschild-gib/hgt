import GaloisForLFunctions.HTGeometry.CompactAbelianStoneWeierstrass

/-!
# Characters generate the topology of a compact abelian group

Every neighbourhood of the origin contains a set cut out by finitely many characters.

The characters separate points, so the closed sets `{x | χ x = 1}` intersect in `{0}`; compactness
turns that into a finite subfamily whose intersection already lies inside the neighbourhood, and a
second compactness argument replaces the exact equalities by a tolerance.

This is the refinement property that lets a compact abelian group be treated as an inverse limit of
its finite-character quotients.
-/

open Set Topology

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- **Finitely many characters cut out a neighbourhood basis at the origin.** -/
theorem exists_finite_char_nbhd {U : Set G} (hUopen : IsOpen U) (hU0 : (0 : G) ∈ U) :
    ∃ (t : Finset C(G, ℂ)) (δ : ℝ), 0 < δ ∧ (∀ χ ∈ t, IsGroupChar χ) ∧
      {x : G | ∀ χ ∈ t, ‖χ x - 1‖ ≤ δ} ⊆ U := by
  classical
  have hcompl : IsCompact (Uᶜ) := (hUopen.isClosed_compl).isCompact
  -- step one: finitely many characters already isolate the origin inside `U`
  set K : {χ : C(G, ℂ) // IsGroupChar χ} → Set G := fun χ => {x : G | (χ : C(G, ℂ)) x = 1} with hK
  have hKclosed : ∀ χ, IsClosed (K χ) := by
    intro χ
    exact isClosed_eq (χ : C(G, ℂ)).continuous continuous_const
  have hKinter : Uᶜ ∩ ⋂ χ, K χ = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hx0 : x = 0 := by
      by_contra hne
      obtain ⟨χ, hcont, hmul, hnorm, hne1⟩ := exists_character_ne_one (G := G) (g := x) hne
      have hmem : x ∈ K ⟨⟨χ, hcont⟩, ⟨hmul, hnorm⟩⟩ := by
        have := hx.2
        rw [mem_iInter] at this
        exact this _
      exact hne1 hmem
    exact hx.1 (hx0 ▸ hU0)
  obtain ⟨t0, ht0⟩ := hcompl.elim_finite_subfamily_closed K hKclosed hKinter
  set t : Finset C(G, ℂ) :=
    t0.image (fun χ : {χ : C(G, ℂ) // IsGroupChar χ} => (χ : C(G, ℂ))) with ht
  have htchar : ∀ χ ∈ t, IsGroupChar χ := by
    intro χ hχ
    rw [ht, Finset.mem_image] at hχ
    obtain ⟨ψ, -, rfl⟩ := hχ
    exact ψ.2
  -- step two: a tolerance suffices
  set Z : ℕ → Set G := fun m => {x : G | ∀ χ ∈ t, ‖χ x - 1‖ ≤ 1 / (m + 1)} with hZ
  have hZclosed : ∀ m, IsClosed (Z m) := by
    intro m
    have : Z m = ⋂ χ ∈ t, {x : G | ‖χ x - 1‖ ≤ 1 / (m + 1)} := by
      ext x
      simp [hZ]
    rw [this]
    refine isClosed_biInter fun χ _ => ?_
    exact isClosed_le ((χ.continuous.sub continuous_const).norm) continuous_const
  have hZanti : ∀ {m n : ℕ}, m ≤ n → Z n ⊆ Z m := by
    intro m n hmn x hx χ hχ
    refine le_trans (hx χ hχ) ?_
    have hm : (0 : ℝ) < m + 1 := by positivity
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [div_le_div_iff₀ hn hm]
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hZinter : Uᶜ ∩ ⋂ m, Z m = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxall : ∀ χ ∈ t, χ x = 1 := by
      intro χ hχ
      have hle : ∀ m : ℕ, ‖χ x - 1‖ ≤ 1 / (m + 1) := by
        intro m
        have h2 := hx.2
        rw [mem_iInter] at h2
        exact h2 m χ hχ
      by_contra hne
      have hpos : 0 < ‖χ x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact absurd (hle m) (not_le.mpr hm)
    have hxK : x ∈ ⋂ χ ∈ t0, K χ := by
      rw [mem_iInter₂]
      intro χ hχ
      have hmem : (χ : C(G, ℂ)) ∈ t := Finset.mem_image_of_mem _ hχ
      exact hxall _ hmem
    exact (eq_empty_iff_forall_notMem.mp ht0 x) ⟨hx.1, hxK⟩
  obtain ⟨s, hs⟩ := hcompl.elim_finite_subfamily_closed Z hZclosed hZinter
  by_cases hsempty : s.Nonempty
  · set M : ℕ := s.max' hsempty with hM
    refine ⟨t, 1 / (M + 1), by positivity, htchar, ?_⟩
    intro x hx
    by_contra hxU
    have hxc : x ∈ Uᶜ := hxU
    have hxZ : x ∈ ⋂ m ∈ s, Z m := by
      rw [mem_iInter₂]
      intro m hm
      exact hZanti (s.le_max' m hm) hx
    exact (eq_empty_iff_forall_notMem.mp hs x) ⟨hxc, hxZ⟩
  · refine ⟨t, 1, one_pos, htchar, ?_⟩
    intro x _
    by_contra hxU
    have hxc : x ∈ Uᶜ := hxU
    have hxZ : x ∈ ⋂ m ∈ s, Z m := by
      rw [Finset.not_nonempty_iff_eq_empty] at hsempty
      rw [hsempty]
      simp
    exact (eq_empty_iff_forall_notMem.mp hs x) ⟨hxc, hxZ⟩

/-- **The character neighbourhood basis at an arbitrary point.**  Translating the origin version,
every neighbourhood of `x` contains a set cut out by finitely many characters around `x`. -/
theorem exists_finite_char_nbhd_at (x : G) {U : Set G} (hUopen : IsOpen U) (hxU : x ∈ U) :
    ∃ (t : Finset C(G, ℂ)) (δ : ℝ), 0 < δ ∧ (∀ χ ∈ t, IsGroupChar χ) ∧
      {y : G | ∀ χ ∈ t, ‖χ y - χ x‖ ≤ δ} ⊆ U := by
  classical
  set V : Set G := {z : G | z + x ∈ U} with hV
  have hVopen : IsOpen V := hUopen.preimage (continuous_id.add continuous_const)
  have hV0 : (0 : G) ∈ V := by
    show (0 : G) + x ∈ U
    rwa [zero_add]
  obtain ⟨t, δ, hδ, htchar, hsub⟩ := exists_finite_char_nbhd hVopen hV0
  refine ⟨t, δ, hδ, htchar, fun y hy => ?_⟩
  have hz : (y - x) ∈ {z : G | ∀ χ ∈ t, ‖χ z - 1‖ ≤ δ} := by
    intro χ hχ
    have hchar := htchar χ hχ
    have hxne : χ x ≠ 0 := by
      intro h0
      have hone := hchar.norm_one x
      rw [h0, norm_zero] at hone
      exact zero_ne_one hone
    have hmul : χ (y - x) * χ x = χ y := by
      rw [← hchar.map_add]
      congr 1
      abel
    have hval : χ (y - x) - 1 = (χ y - χ x) / χ x := by
      field_simp
      linear_combination hmul
    rw [hval, norm_div, hchar.norm_one x, div_one]
    exact hy χ hχ
  have hmem := hsub hz
  show y ∈ U
  have hyx : y - x + x = y := by abel
  rwa [hV, Set.mem_setOf_eq, hyx] at hmem

/-- **Uniform character refinement.**  Every finite open cover of a compact abelian group is
refined by the boxes of a single finite character packet. -/
theorem exists_uniform_char_refinement {κ : Type} [Fintype κ] (U : κ → Set G)
    (hopen : ∀ k, IsOpen (U k)) (hcov : ⋃ k, U k = Set.univ) :
    ∃ (t : Finset C(G, ℂ)) (δ : ℝ), 0 < δ ∧ (∀ χ ∈ t, IsGroupChar χ) ∧
      ∀ x : G, ∃ k, {y : G | ∀ χ ∈ t, ‖χ y - χ x‖ ≤ δ} ⊆ U k := by
  classical
  have hmem : ∀ x : G, ∃ k, x ∈ U k := by
    intro x
    have : x ∈ ⋃ k, U k := by rw [hcov]; trivial
    exact Set.mem_iUnion.mp this
  choose k hk using hmem
  have hbox : ∀ x : G, ∃ (t : Finset C(G, ℂ)) (δ : ℝ), 0 < δ ∧ (∀ χ ∈ t, IsGroupChar χ) ∧
      {y : G | ∀ χ ∈ t, ‖χ y - χ x‖ ≤ δ} ⊆ U (k x) :=
    fun x => exists_finite_char_nbhd_at x (hopen (k x)) (hk x)
  choose tx δx hδpos hchar hsub using hbox
  set O : G → Set G := fun x => {y : G | ∀ χ ∈ tx x, ‖χ y - χ x‖ < δx x / 2} with hO
  have hOopen : ∀ x, IsOpen (O x) := by
    intro x
    have hEq : O x = ⋂ χ ∈ tx x, {y : G | ‖χ y - χ x‖ < δx x / 2} := by
      ext y
      simp [hO]
    rw [hEq]
    exact isOpen_biInter_finset fun χ _ =>
      isOpen_lt ((χ.continuous.sub continuous_const).norm) continuous_const
  have hOcov : (Set.univ : Set G) ⊆ ⋃ x, O x := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    intro χ _
    have : χ y - χ y = 0 := sub_self _
    rw [this, norm_zero]
    exact half_pos (hδpos y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hOopen hOcov
  have hsne : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have h0 : (0 : G) ∈ ⋃ x ∈ s, O x := hs (Set.mem_univ _)
    rw [hempty] at h0
    simp at h0
  refine ⟨s.biUnion tx, s.inf' hsne (fun x => δx x / 2), ?_, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun x _ => half_pos (hδpos x)
  · intro χ hχ
    rw [Finset.mem_biUnion] at hχ
    obtain ⟨x, _, hx⟩ := hχ
    exact hchar x χ hx
  · intro y
    have hy : y ∈ ⋃ x ∈ s, O x := hs (Set.mem_univ _)
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨x, hxs, hyx⟩ := hy
    refine ⟨k x, fun z hz => ?_⟩
    refine hsub x ?_
    intro χ hχ
    have hχt : χ ∈ s.biUnion tx := Finset.mem_biUnion.mpr ⟨x, hxs, hχ⟩
    have h1 : ‖χ z - χ y‖ ≤ δx x / 2 :=
      le_trans (hz χ hχt) (Finset.inf'_le (fun x => δx x / 2) hxs)
    have h2 : ‖χ y - χ x‖ < δx x / 2 := hyx χ hχ
    calc ‖χ z - χ x‖ = ‖(χ z - χ y) + (χ y - χ x)‖ := by ring_nf
      _ ≤ ‖χ z - χ y‖ + ‖χ y - χ x‖ := norm_add_le _ _
      _ ≤ δx x := by linarith

end

end CompactAbelian

end GaloisForLFunctions
