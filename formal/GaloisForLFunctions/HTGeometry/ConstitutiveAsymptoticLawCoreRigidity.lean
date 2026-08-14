import GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCore

/-!
# Strict nonlinear exchange rigidity for asymptotic law cores

A convergent scalar energy history has singleton scalar law core. If a strictly
convex energy loses no information when passing through tail-law formation,
then the source law core itself must be a singleton.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous convex energy whose values converge to `c` is at most `c` on
the complete asymptotic law core. Convex formation can dissipate energy, but it
cannot create energy above the limiting tail level. -/
theorem convex_energy_le_limit_on_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hx : ∀ n, x n ∈ K)
    (W : E → ℝ) (hW : ConvexOn ℝ K W) (hWcont : Continuous W) {c : ℝ}
    (hWx : Tendsto (W ∘ x) atTop (𝓝 c)) {y : E}
    (hy : y ∈ asymptoticLawCore x) :
    W y ≤ c := by
  by_contra hnot
  have hcy : c < W y := lt_of_not_ge hnot
  let ε : ℝ := (W y - c) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hev : ∀ᶠ n in atTop, W (x n) < c + ε :=
    (tendsto_order.1 hWx).2 (c + ε) (lt_add_of_pos_right c hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set E := {z ∈ K | W z ≤ c + ε}
  have htail : lawTail x N ⊆ S := by
    rintro z ⟨n, hn, rfl⟩
    exact ⟨hx n, (hN n hn).le⟩
  have hSconv : Convex ℝ S := by
    simpa only [S] using hW.convex_le (c + ε)
  have hSclosed : IsClosed S := by
    dsimp only [S]
    exact hK.isClosed.inter (isClosed_Iic.preimage hWcont)
  have hyS : y ∈ S :=
    closedConvexHull_min htail hSconv hSclosed (Set.mem_iInter.mp hy N)
  dsimp only [S] at hyS
  dsimp [ε] at hyS
  linarith

/-- **Strict Jensen dissipation witness.** If the source law core is not a
singleton while a continuous strictly convex energy converges, then some
formed source law has energy strictly below the limiting scalar law and hence
is absent from the scalar energy core. This is a concrete nonlinear formation
exchange defect, not merely a failure of a set equality. -/
theorem exists_strictConvex_formationDissipation_of_nonsingleton
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hx : ∀ n, x n ∈ K)
    (W : E → ℝ) (hW : StrictConvexOn ℝ K W) (hWcont : Continuous W) {c : ℝ}
    (hWx : Tendsto (W ∘ x) atTop (𝓝 c))
    (hmulti : ¬ ∃ a, asymptoticLawCore x = {a}) :
    ∃ m, m ∈ asymptoticLawCore x ∧ W m < c ∧
      W m ∉ asymptoticLawCore (W ∘ x) := by
  obtain ⟨a, ha⟩ := asymptoticLawCore_nonempty hK hW.1 hx
  have hnotSub : ¬asymptoticLawCore x ⊆ {a} := by
    intro hsub
    apply hmulti
    exact ⟨a, Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr ha)⟩
  obtain ⟨y, hy, hya⟩ := Set.not_subset.1 hnotSub
  have hne : a ≠ y := by
    intro h
    apply hya
    simp [h]
  let m : E := (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • y
  have hm : m ∈ asymptoticLawCore x := by
    exact (asymptoticLawCore_convex x) ha hy (by norm_num) (by norm_num) (by norm_num)
  have haK : a ∈ K :=
    asymptoticLawCore_subset_of_compactConvex hW.1 hK.isClosed hx ha
  have hyK : y ∈ K :=
    asymptoticLawCore_subset_of_compactConvex hW.1 hK.isClosed hx hy
  have hWa : W a ≤ c :=
    convex_energy_le_limit_on_asymptoticLawCore hK hx W hW.convexOn hWcont hWx ha
  have hWy : W y ≤ c :=
    convex_energy_le_limit_on_asymptoticLawCore hK hx W hW.convexOn hWcont hWx hy
  have hlt := hW.2 haK hyK hne (by norm_num : 0 < (2 : ℝ)⁻¹)
    (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
  change W m < (2 : ℝ)⁻¹ • W a + (2 : ℝ)⁻¹ • W y at hlt
  have hmc : W m < c := by
    norm_num [smul_eq_mul] at hlt
    linarith
  have henergy : asymptoticLawCore (W ∘ x) = {c} :=
    asymptoticLawCore_eq_singleton_of_tendsto hWx
  refine ⟨m, hm, hmc, ?_⟩
  rw [henergy, Set.mem_singleton_iff]
  exact ne_of_lt hmc

/-- Every compact formation with a convergent continuous strictly convex
energy has exactly the field-level alternative needed for selection: either
the complete law core is one law, or a formed law exhibits strict energy
dissipation and is invisible to the scalar energy core. -/
theorem asymptoticLawCore_singleton_or_strictConvex_dissipation
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hx : ∀ n, x n ∈ K)
    (W : E → ℝ) (hW : StrictConvexOn ℝ K W) (hWcont : Continuous W) {c : ℝ}
    (hWx : Tendsto (W ∘ x) atTop (𝓝 c)) :
    (∃ a, asymptoticLawCore x = {a}) ∨
      ∃ m, m ∈ asymptoticLawCore x ∧ W m < c ∧
        W m ∉ asymptoticLawCore (W ∘ x) := by
  by_cases hsingle : ∃ a, asymptoticLawCore x = {a}
  · exact Or.inl hsingle
  · exact Or.inr
      (exists_strictConvex_formationDissipation_of_nonsingleton
        hK hx W hW hWcont hWx hsingle)

/-- **Global formation/properness selection law.** A continuous strictly convex
energy with compact sublevel sets supplies its own compact formation domain.
Along every history whose energy converges, either the complete asymptotic law
core is one law, or convex formation produces a strict energy-dissipation law
that the scalar energy history cannot form. No compact carrier is assumed as
input. -/
theorem properStrictConvex_asymptoticLawCore_singleton_or_dissipation
    (W : E → ℝ) (hW : StrictConvexOn ℝ Set.univ W)
    (hWcont : Continuous W)
    (hProper : ∀ r : ℝ, IsCompact {z : E | W z ≤ r})
    {x : ℕ → E} {c : ℝ} (hWx : Tendsto (W ∘ x) atTop (𝓝 c)) :
    (∃ a, asymptoticLawCore x = {a}) ∨
      ∃ m, m ∈ asymptoticLawCore x ∧ W m < c ∧
        W m ∉ asymptoticLawCore (W ∘ x) := by
  obtain ⟨C, hC⟩ := hWx.bddAbove_range
  let K : Set E := {z : E | W z ≤ C}
  have hxK : ∀ n, x n ∈ K := by
    intro n
    exact hC ⟨n, rfl⟩
  have hK : IsCompact K := by
    simpa only [K] using hProper C
  have hWK : StrictConvexOn ℝ K W := by
    constructor
    · simpa [K] using hW.convexOn.convex_le C
    · intro u hu v hv huv a b ha hb hab
      exact hW.2 (Set.mem_univ u) (Set.mem_univ v) huv ha hb hab
  exact asymptoticLawCore_singleton_or_strictConvex_dissipation
    hK hxK W hWK hWcont hWx

/-- **Strict nonlinear formation-exchange rigidity.** If a strictly convex
energy has a convergent history and every energy value of a formed source law
is still formable from the scalar energy history, then the source law core is a
singleton. Thus any nontrivial core forces a strict nonlinear exchange defect. -/
theorem asymptoticLawCore_singleton_of_strictConvex_noLoss
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hx : ∀ n, x n ∈ K)
    (W : E → ℝ) (hW : StrictConvexOn ℝ K W) {c : ℝ}
    (hWx : Tendsto (W ∘ x) atTop (𝓝 c))
    (hNoLoss : W '' asymptoticLawCore x ⊆ asymptoticLawCore (W ∘ x)) :
    ∃ a, asymptoticLawCore x = {a} := by
  obtain ⟨a, ha⟩ := asymptoticLawCore_nonempty hK hW.1 hx
  refine ⟨a, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    have haK : a ∈ K :=
      asymptoticLawCore_subset_of_compactConvex hW.1 hK.isClosed hx ha
    have hyK : y ∈ K :=
      asymptoticLawCore_subset_of_compactConvex hW.1 hK.isClosed hx hy
    have henergy : asymptoticLawCore (W ∘ x) = {c} :=
      asymptoticLawCore_eq_singleton_of_tendsto hWx
    have hWa : W a = c := by
      have : W a ∈ asymptoticLawCore (W ∘ x) := hNoLoss ⟨a, ha, rfl⟩
      rw [henergy] at this
      exact Set.mem_singleton_iff.mp this
    have hWy : W y = c := by
      have : W y ∈ asymptoticLawCore (W ∘ x) := hNoLoss ⟨y, hy, rfl⟩
      rw [henergy] at this
      exact Set.mem_singleton_iff.mp this
    by_contra hay
    have hne : a ≠ y := by
      intro h
      apply hay
      simp [h]
    let m : E := (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • y
    have hm : m ∈ asymptoticLawCore x := by
      exact (asymptoticLawCore_convex x) ha hy (by norm_num) (by norm_num) (by norm_num)
    have hWm : W m = c := by
      have : W m ∈ asymptoticLawCore (W ∘ x) := hNoLoss ⟨m, hm, rfl⟩
      rw [henergy] at this
      exact Set.mem_singleton_iff.mp this
    have hlt := hW.2 haK hyK hne (by norm_num : 0 < (2 : ℝ)⁻¹)
      (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
    change W m < (2 : ℝ)⁻¹ • W a + (2 : ℝ)⁻¹ • W y at hlt
    rw [hWm, hWa, hWy] at hlt
    norm_num [smul_eq_mul] at hlt
    linarith
  · rintro y rfl
    exact ha

/-- Exact nonlinear formation exchange is a sufficient no-loss hypothesis. -/
theorem asymptoticLawCore_singleton_of_strictConvex_exchange
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hx : ∀ n, x n ∈ K)
    (W : E → ℝ) (hW : StrictConvexOn ℝ K W) {c : ℝ}
    (hWx : Tendsto (W ∘ x) atTop (𝓝 c))
    (hExchange : W '' asymptoticLawCore x = asymptoticLawCore (W ∘ x)) :
    ∃ a, asymptoticLawCore x = {a} :=
  asymptoticLawCore_singleton_of_strictConvex_noLoss hK hx W hW hWx hExchange.le

/-- Global compact-sublevel version of nonlinear no-loss selection. Properness
of the energy manufactures the compact carrier needed by strict-convex
formation rigidity. -/
theorem properStrictConvex_asymptoticLawCore_singleton_of_noLoss
    (W : E → ℝ) (hW : StrictConvexOn ℝ Set.univ W)
    (hProper : ∀ r : ℝ, IsCompact {z : E | W z ≤ r})
    {x : ℕ → E} {c : ℝ} (hWx : Tendsto (W ∘ x) atTop (𝓝 c))
    (hNoLoss : W '' asymptoticLawCore x ⊆ asymptoticLawCore (W ∘ x)) :
    ∃ a, asymptoticLawCore x = {a} := by
  obtain ⟨C, hC⟩ := hWx.bddAbove_range
  let K : Set E := {z : E | W z ≤ C}
  have hxK : ∀ n, x n ∈ K := by
    intro n
    exact hC ⟨n, rfl⟩
  have hK : IsCompact K := by
    simpa only [K] using hProper C
  have hWK : StrictConvexOn ℝ K W :=
    hW.subset (by simp [K]) (by simpa [K] using hW.convexOn.convex_le C)
  exact asymptoticLawCore_singleton_of_strictConvex_noLoss
    hK hxK W hWK hWx hNoLoss

end GaloisForLFunctions.HTGeometry
