import GaloisForLFunctions.HTGeometry.FirstOrderRelationLocalUniqueness

/-!
# Repeated regular values of a first-order algebraic relation near infinity

Let `φ` be holomorphic near infinity with dense image on every neighbourhood of infinity, and let
`D` be an observable with `Q(φ, D) = 0` for a nonzero `Q ∈ ℂ[X][Y]`.  Suppose that away from a
set with no accumulation point in the domain, `φ' ≠ 0` and `∂_Y Q (φ, D) ≠ 0` ("good" points).

Then arbitrarily far out there are two good points `z₁`, `z₂` with `‖z₂‖ > ‖z₁‖ + 1` on which `φ`
takes the same value and `D` takes the same value.

The proof builds, one after another, `N + 1 = deg_Y Q + 1` small discs of good points escaping to
infinity, together with a nested sequence of nonempty open sets of values each of which is attained
in every disc so far (density supplies the next disc, the open mapping theorem the next open set).
A common value `w` with `Q(w, ·) ≠ 0` has `N + 1` distinct good preimages, but `D` can take only
the `≤ N` roots of `Q(w, ·)` there; two preimages share their `D`-value.
-/

open Filter Topology Metric Set Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A point is good for `(φ, D, Q)`. -/
def RelGood (φ D : ℂ → ℂ) (Q : Polynomial (Polynomial ℂ)) (z : ℂ) : Prop :=
  deriv φ z ≠ 0 ∧ relEval (derivative Q) (φ z) (D z) ≠ 0

/-- Good points are dense in every nonempty open subset of the domain when the bad points do not
accumulate. -/
theorem exists_relGood_mem_of_isOpen {φ D : ℂ → ℂ} {Q : Polynomial (Polynomial ℂ)} {Ω U : Set ℂ}
    (hgood : ∀ z ∈ Ω, ∀ᶠ y in 𝓝[≠] z, RelGood φ D Q y) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (hne : U.Nonempty) : ∃ y ∈ U, RelGood φ D Q y := by
  obtain ⟨z, hz⟩ := hne
  have h1 : ∀ᶠ y in 𝓝[≠] z, y ∈ U := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz)
  obtain ⟨y, hyU, hyg⟩ := ((h1.and (hgood z (hUΩ hz))).exists)
  exact ⟨y, hyU, hyg⟩

/-- **Repeated regular values.** -/
theorem exists_repeated_relGood_value {φ D : ℂ → ℂ} {R₀ : ℝ}
    (hφ : DifferentiableOn ℂ φ {z | R₀ < ‖z‖}) {Q : Polynomial (Polynomial ℂ)} (hQ : Q ≠ 0)
    (hrel : ∀ z : ℂ, R₀ < ‖z‖ → relEval Q (φ z) (D z) = 0)
    (hgood : ∀ z ∈ {z : ℂ | R₀ < ‖z‖}, ∀ᶠ y in 𝓝[≠] z, RelGood φ D Q y)
    (hdense : ∀ R : ℝ, Dense (φ '' {z | R < ‖z‖})) (R : ℝ) :
    ∃ z₁ z₂ : ℂ, R < ‖z₁‖ ∧ ‖z₁‖ + 1 < ‖z₂‖ ∧ R₀ < ‖z₁‖ ∧ φ z₁ = φ z₂ ∧ D z₁ = D z₂ ∧
      RelGood φ D Q z₁ := by
  classical
  set Ω : Set ℂ := {z | R₀ < ‖z‖} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt continuous_const continuous_norm
  set R₁ := max R R₀ with hR₁
  -- the inductive construction of discs
  have key : ∀ k : ℕ, ∃ (V : Set ℂ) (c : ℕ → ℂ), IsOpen V ∧ V.Nonempty ∧
      (∀ i < k, R₁ + 2 < ‖c i‖) ∧ (∀ i j, i < j → j < k → ‖c i‖ + 2 < ‖c j‖) ∧
      ∀ w ∈ V, ∀ i < k, ∃ ζ ∈ ball (c i) (1 / 2), ζ ∈ Ω ∧ RelGood φ D Q ζ ∧ φ ζ = w := by
    intro k
    induction k with
    | zero => exact ⟨univ, fun _ => 0, isOpen_univ, univ_nonempty, by simp, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨V, c, hVo, hVne, hcR, hcsep, hVc⟩ := ih
      set R' := |R₁| + 2 + ∑ i ∈ Finset.range k, ‖c i‖ with hR'
      have hR'i : ∀ i < k, ‖c i‖ + 2 ≤ R' := by
        intro i hi
        have h1 : ‖c i‖ ≤ ∑ j ∈ Finset.range k, ‖c j‖ :=
          Finset.single_le_sum (f := fun j => ‖c j‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_range.mpr hi)
        have h2 := abs_nonneg R₁
        linarith
      have hR'1 : R₁ + 2 ≤ R' := by
        have h1 := Finset.sum_nonneg (s := Finset.range k) (fun i _ => norm_nonneg (c i))
        have h2 := le_abs_self R₁
        linarith
      -- a good far point with value in `V`
      have hfar : IsOpen ({z : ℂ | R' < ‖z‖} ∩ (Ω ∩ φ ⁻¹' V)) :=
        (isOpen_lt continuous_const continuous_norm).inter
          (hφ.continuousOn.isOpen_inter_preimage hΩo hVo)
      have hfarne : ({z : ℂ | R' < ‖z‖} ∩ (Ω ∩ φ ⁻¹' V)).Nonempty := by
        obtain ⟨_, ⟨hwV, z, hz, rfl⟩⟩ := (hdense (max R' R₀)).inter_open_nonempty V hVo hVne
        exact ⟨z, show R' < ‖z‖ from lt_of_le_of_lt (le_max_left _ _) hz,
          by rw [hΩ, mem_setOf_eq]; exact lt_of_le_of_lt (le_max_right _ _) hz, hwV⟩
      obtain ⟨z', ⟨hz'R, hz'Ω, hz'V⟩, hz'g⟩ :=
        exists_relGood_mem_of_isOpen hgood hfar (fun z hz => hz.2.1) hfarne
      have hz'R' : R' < ‖z'‖ := hz'R
      -- a small disc of good points mapped into `V`
      obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ : ∃ ρ₁ > 0, ∀ y ∈ ball z' ρ₁, y ∈ Ω ∧ RelGood φ D Q y := by
        have hev : ∀ᶠ y in 𝓝 z', y ∈ Ω ∧ RelGood φ D Q y := by
          have hpunct := hgood z' hz'Ω
          rw [eventually_nhdsWithin_iff] at hpunct
          filter_upwards [hpunct, hΩo.mem_nhds hz'Ω] with y hy hyΩ
          refine ⟨hyΩ, ?_⟩
          by_cases hyz : y = z'
          · rw [hyz]; exact hz'g
          · exact hy hyz
        obtain ⟨ρ₁, hρ₁, h⟩ := Metric.eventually_nhds_iff_ball.mp hev
        exact ⟨ρ₁, hρ₁, h⟩
      have hanaz : AnalyticAt ℂ φ z' := (hφ.analyticOnNhd hΩo) z' hz'Ω
      obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ : ∃ ρ₂ > 0, ∀ y ∈ ball z' ρ₂, φ y ∈ V := by
        have := hanaz.continuousAt.preimage_mem_nhds (hVo.mem_nhds hz'V)
        obtain ⟨ρ₂, hρ₂, h⟩ := Metric.mem_nhds_iff.mp this
        exact ⟨ρ₂, hρ₂, fun y hy => h hy⟩
      set ρ := min (min ρ₁ ρ₂) (1 / 2) with hρ
      have hρpos : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) (by norm_num)
      obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, ball (φ z') ε ⊆ φ '' ball z' ρ := by
        rcases hanaz.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
        · exfalso
          apply hz'g.1
          have h1 : deriv φ z' = deriv (fun _ : ℂ => φ z') z' := Filter.EventuallyEq.deriv_eq hconst
          simpa using h1
        · exact Metric.mem_nhds_iff.mp (hmap (image_mem_map (ball_mem_nhds z' hρpos)))
      refine ⟨ball (φ z') ε ∩ V, fun i => if i = k then z' else c i, isOpen_ball.inter hVo,
        ⟨φ z', mem_ball_self hε, hz'V⟩, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · simp only [if_pos hik]; linarith
        · simp only [if_neg hik]; exact hcR i (by omega)
      · intro i j hij hj
        by_cases hjk : j = k
        · have hik : i ≠ k := by omega
          simp only [if_pos hjk, if_neg hik]
          have := hR'i i (by omega)
          linarith
        · have hik : i ≠ k := by omega
          simp only [if_neg hjk, if_neg hik]
          exact hcsep i j hij (by omega)
      · intro w hw i hi
        by_cases hik : i = k
        · simp only [if_pos hik]
          obtain ⟨ζ, hζ, hζw⟩ := hεsub hw.1
          have hζρ₁ : ζ ∈ ball z' ρ₁ := ball_subset_ball
            ((min_le_left _ _).trans (min_le_left _ _)) hζ
          obtain ⟨hζΩ, hζg⟩ := hρ₁sub ζ hζρ₁
          exact ⟨ζ, ball_subset_ball (min_le_right _ _) hζ, hζΩ, hζg, hζw⟩
        · simp only [if_neg hik]
          exact hVc w hw.2 i (by omega)
  -- the pigeonhole at level `deg_Y Q + 1`
  set N := Q.natDegree with hN
  obtain ⟨V, c, hVo, hVne, hcR, hcsep, hVc⟩ := key (N + 1)
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  obtain ⟨w, hwV, hwlc⟩ : ∃ w ∈ V, (Q.leadingCoeff).eval w ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : V ⊆ ((Q.leadingCoeff).roots.toFinset : Set ℂ) := by
      intro w hw
      simp [mem_roots hlc, hall w hw]
    obtain ⟨z, hz⟩ := hVne
    exact (infinite_of_mem_nhds z (hVo.mem_nhds hz)).mono hsub
      (Finset.finite_toSet _)
  choose ζ hζball hζΩ hζg hζw using fun i (hi : i < N + 1) => hVc w hwV i hi
  set q := Q.map (evalRingHom w) with hq
  have hq0 : q ≠ 0 := by
    intro h0
    have := congrArg leadingCoeff h0
    rw [hq, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simpa using hwlc)] at this
    simp only [coe_evalRingHom, leadingCoeff_zero] at this
    exact hwlc this
  have hmaps : Set.MapsTo (fun i => if hi : i < N + 1 then D (ζ i hi) else 0)
      (Finset.range (N + 1) : Set ℕ) (q.roots.toFinset : Set ℂ) := by
    intro i hi
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    simp only [dif_pos hi', Finset.mem_coe, Multiset.mem_toFinset, mem_roots hq0, IsRoot.def]
    have := hrel (ζ i hi') (hζΩ i hi')
    rwa [hζw i hi', relEval] at this
  have hcard : q.roots.toFinset.card < (Finset.range (N + 1)).card := by
    rw [Finset.card_range]
    calc q.roots.toFinset.card ≤ q.roots.card := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := card_roots' q
      _ ≤ N := natDegree_map_le
      _ < N + 1 := Nat.lt_succ_self N
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hi' : i < N + 1 := Finset.mem_range.mp hi
  have hj' : j < N + 1 := Finset.mem_range.mp hj
  simp only [dif_pos hi', dif_pos hj'] at heq
  -- order the two indices
  have hnorm : ∀ a b (ha : a < N + 1) (hb : b < N + 1), a < b →
      ‖ζ a ha‖ + 1 < ‖ζ b hb‖ ∧ R < ‖ζ a ha‖ := by
    intro a b ha hb hab
    have h1 := hcsep a b hab hb
    have hza := hζball a ha
    have hzb := hζball b hb
    rw [mem_ball, dist_eq_norm] at hza hzb
    have ha1 : ‖ζ a ha‖ ≤ ‖c a‖ + 1 / 2 := by
      have := norm_le_insert' (ζ a ha) (c a)
      linarith [norm_sub_rev (ζ a ha) (c a)]
    have hb1 : ‖c b‖ - 1 / 2 ≤ ‖ζ b hb‖ := by
      have := norm_sub_norm_le (c b) (ζ b hb)
      rw [norm_sub_rev] at this
      linarith
    have hca := hcR a ha
    have ha2 : ‖c a‖ - 1 / 2 ≤ ‖ζ a ha‖ := by
      have := norm_sub_norm_le (c a) (ζ a ha)
      rw [norm_sub_rev] at this
      linarith
    have hRR₁ : R ≤ R₁ := le_max_left _ _
    constructor <;> linarith
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨h1, h2⟩ := hnorm i j hi' hj' hlt
    exact ⟨ζ i hi', ζ j hj', h2, h1, hζΩ i hi', (hζw i hi').trans (hζw j hj').symm, heq,
      hζg i hi'⟩
  · obtain ⟨h1, h2⟩ := hnorm j i hj' hi' hgt
    exact ⟨ζ j hj', ζ i hi', h2, h1, hζΩ j hj', (hζw j hj').trans (hζw i hi').symm, heq.symm,
      hζg j hj'⟩

end GaloisForLFunctions.HTGeometry
