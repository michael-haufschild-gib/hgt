import GaloisForLFunctions.HTGeometry.ZeroDivisorCount

/-!
# The zero divisor as a continuous observable

The zero divisor of a holomorphic function, paired with a continuous test function of compact
support, is a finite sum of the multiplicities weighted by the values of the test function at the
zeros.  Under a uniform perturbation of the function the zeros move continuously: away from the
zeros of the limit the perturbation cannot vanish, and around each of them the total multiplicity is
preserved because it is a contour integral with integer values.

The pairing is therefore continuous for uniform convergence, which is the statement that the
Poincaré–Lelong divisor map is continuous — the input a divisor frequency law consumes.
-/

open Complex Metric Set Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### The pairing -/

/-- The zero divisor of `f`, paired with a test function. -/
noncomputable def divisorPairing (f φ : ℂ → ℂ) : ℂ := ∑ᶠ a : ℂ, (zeroMult f a : ℂ) * φ a

/-- A point of positive multiplicity is a zero. -/
theorem eq_zero_of_zeroMult_ne_zero {f : ℂ → ℂ} {a : ℂ} (h : zeroMult f a ≠ 0) : f a = 0 := by
  refine apply_eq_zero_of_analyticOrderAt_ne_zero ?_
  intro h0
  exact h (by rw [zeroMult, h0]; rfl)

/-- The pairing is a finite sum over any finite set containing the relevant zeros. -/
theorem divisorPairing_eq_sum {f φ : ℂ → ℂ} {s : Finset ℂ}
    (hs : ∀ a : ℂ, zeroMult f a ≠ 0 → φ a ≠ 0 → a ∈ s) :
    divisorPairing f φ = ∑ a ∈ s, (zeroMult f a : ℂ) * φ a := by
  refine finsum_eq_finsetSum_of_support_subset _ ?_
  intro a ha
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ha
  have h1 : zeroMult f a ≠ 0 := by
    intro h0
    exact ha.1 (by rw [h0]; simp)
  exact hs a h1 ha.2

/-! ### Zeros are finite on compact sets -/

/-- **The zeros of a nowhere locally trivial holomorphic function are finite on every compact
set.** -/
theorem finite_zeros_of_isCompact {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hiso : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, f w = 0))
    {S : Set ℂ} (hS : IsCompact S) (hSU : S ⊆ U) :
    (S ∩ {z | f z = 0}).Finite := by
  classical
  have han : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  -- around each point of `S` the only possible zero is the point itself
  have hloc : ∀ z ∈ S, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ ∀ w ∈ V, f w = 0 → w = z := by
    intro z hz
    rcases (han z (hSU hz)).eventually_eq_zero_or_eventually_ne_zero with hcon | hne
    · exact absurd hcon (hiso z (hSU hz))
    · rw [eventually_nhdsWithin_iff] at hne
      obtain ⟨V, hVsub, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hne
      refine ⟨V, hVopen, hzV, fun w hw hw0 => ?_⟩
      by_contra hwz
      exact hVsub hw hwz hw0
  choose V hVopen hzV hVzero using hloc
  obtain ⟨T, hTsub⟩ := hS.elim_finite_subcover (fun z : S => V z z.2)
    (fun z => hVopen z z.2) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hzV z hz⟩)
  refine Set.Finite.subset (T.finite_toSet.image (fun z : S => (z : ℂ))) ?_
  intro w hw
  obtain ⟨z, hz⟩ := mem_iUnion.mp (hTsub hw.1)
  obtain ⟨hzT, hwV⟩ := mem_iUnion.mp hz
  exact ⟨z, hzT, (hVzero z z.2 w hwV hw.2).symm⟩

/-! ### A separating radius for a finite set -/

/-- A radius small enough to separate the points of a finite set. -/
theorem exists_separating_radius (A : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ 4 * δ ≤ ρ ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 4 * δ < dist a b := by
  classical
  set P : Finset (ℂ × ℂ) := (A ×ˢ A).filter (fun p => p.1 ≠ p.2) with hP
  rcases P.eq_empty_or_nonempty with hempty | hne
  · refine ⟨ρ / 4, by positivity, by linarith, fun a ha b hb hab => ?_⟩
    have hmem : (a, b) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
    rw [hempty] at hmem
    exact absurd hmem (by simp)
  · obtain ⟨p, hpP, hpmin⟩ := P.exists_min_image (fun p => dist p.1 p.2) hne
    have hppos : 0 < dist p.1 p.2 := by
      have := (Finset.mem_filter.mp hpP).2
      exact dist_pos.mpr this
    refine ⟨min (ρ / 4) (dist p.1 p.2 / 8), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have : min (ρ / 4) (dist p.1 p.2 / 8) ≤ ρ / 4 := min_le_left _ _
      linarith
    · intro a ha b hb hab
      have hmem : (a, b) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
      have hle : dist p.1 p.2 ≤ dist a b := hpmin (a, b) hmem
      have : min (ρ / 4) (dist p.1 p.2 / 8) ≤ dist p.1 p.2 / 8 := min_le_right _ _
      linarith

/-! ### The local exchange of zeros -/

/-- **Zeros are exchanged locally with the same total multiplicity.**  Around an isolated zero of a
holomorphic function, every sufficiently close holomorphic function has its zeros in the same small
disc, with the same total multiplicity. -/
theorem exists_local_zeroSet {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : ℂ} {δ : ℝ} (hδ : 0 < δ) (hball : closedBall a (2 * δ) ⊆ U)
    (hzero : f a = 0) (honly : ∀ w ∈ closedBall a (2 * δ), f w = 0 → w = a) :
    ∃ ε > 0, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h U →
      (∀ z ∈ closedBall a (2 * δ), ‖h z - f z‖ ≤ ε) →
        ∃ Za : Finset ℂ, (∀ ρ ∈ Za, ρ ∈ ball a δ) ∧
          (∀ z ∈ ball a δ, h z = 0 ↔ z ∈ Za) ∧
          (∑ ρ ∈ Za, zeroMult h ρ) = zeroMult f a := by
  classical
  have hδ2 : δ < 2 * δ := by linarith
  have hsub2 : ball a δ ⊆ closedBall a (2 * δ) := fun w hw => by
    rw [mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le (mem_ball.mp hw) (by linarith))
  have hne : ∀ ζ ∈ sphere a δ, f ζ ≠ 0 := by
    intro ζ hζ h0
    have hζc : ζ ∈ closedBall a (2 * δ) := by
      rw [mem_closedBall, mem_sphere.mp hζ]
      linarith
    have hζa := honly ζ hζc h0
    have hd : dist ζ a = δ := mem_sphere.mp hζ
    rw [hζa, dist_self] at hd
    exact absurd hd.symm (ne_of_gt hδ)
  -- the zero set of `f` inside the small disc is the single point `a`
  obtain ⟨Z₀, hZ₀ball, hZ₀zero, hZ₀sum⟩ :=
    exists_zeroSet_zeroSumBall hδ hδ2 hU hball hf hne
  have hZ₀eq : Z₀ = {a} := by
    ext w
    constructor
    · intro hw
      have hwball := hZ₀ball w hw
      have hw0 : f w = 0 := (hZ₀zero w hwball).mpr hw
      have := honly w (hsub2 hwball) hw0
      simp [this]
    · intro hw
      rw [Finset.mem_singleton] at hw
      subst hw
      exact (hZ₀zero w (mem_ball_self hδ)).mp hzero
  have hfsum : zeroSumBall f a δ = (zeroMult f a : ℂ) := by
    rw [hZ₀sum, hZ₀eq, Finset.sum_singleton]
  obtain ⟨ε, hε, hstable⟩ := exists_eps_zeroSumBall_eq hδ hδ2 hU hball hf hne
  refine ⟨ε, hε, fun h hhd hclose => ?_⟩
  obtain ⟨hhne, hheq⟩ := hstable h hhd hclose
  obtain ⟨Za, hZaball, hZazero, hZasum⟩ :=
    exists_zeroSet_zeroSumBall hδ hδ2 hU hball hhd hhne
  refine ⟨Za, hZaball, hZazero, ?_⟩
  have hcast : ((∑ ρ ∈ Za, zeroMult h ρ : ℕ) : ℂ) = ((zeroMult f a : ℕ) : ℂ) := by
    push_cast
    rw [← hZasum, hheq, hfsum]
  exact_mod_cast hcast

/-! ### Continuity of the pairing -/

/-- **The divisor pairing is continuous.**  For a family of holomorphic functions on an open set,
converging uniformly on that set and with a nowhere locally trivial limit, the zero divisor paired
with a fixed continuous test function of compact support inside the set depends continuously on the
parameter. -/
theorem continuousAt_divisorPairing {U : Set ℂ} (hU : IsOpen U)
    {X : Type*} [TopologicalSpace X] {G : X → ℂ → ℂ} {x₀ : X}
    (hG : ∀ x, DifferentiableOn ℂ (G x) U)
    (hiso : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, G x₀ w = 0))
    (hunif : ∀ ε > 0, ∀ᶠ x in nhds x₀, ∀ z ∈ U, ‖G x z - G x₀ z‖ ≤ ε)
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hKc : IsCompact (tsupport φ)) (hKU : tsupport φ ⊆ U) :
    ContinuousAt (fun x => divisorPairing (G x) φ) x₀ := by
  classical
  set K : Set ℂ := tsupport φ with hKdef
  obtain ⟨ρ, hρ, hρU⟩ := hKc.exists_cthickening_subset_open hU hKU
  set ρ₀ : ℝ := ρ / 4 with hρ₀def
  have hρ₀ : 0 < ρ₀ := by rw [hρ₀def]; positivity
  set K₂ : Set ℂ := cthickening (2 * ρ₀) K with hK₂def
  set K₃ : Set ℂ := cthickening (3 * ρ₀) K with hK₃def
  have hK₂c : IsCompact K₂ := hKc.cthickening
  have hK₃c : IsCompact K₃ := hKc.cthickening
  have hK₃U : K₃ ⊆ U := by
    refine subset_trans (cthickening_mono ?_ K) hρU
    rw [hρ₀def]
    linarith
  have hK₂K₃ : K₂ ⊆ K₃ := cthickening_mono (by linarith) K
  have hKK₂ : K ⊆ K₂ := self_subset_cthickening K
  have hK₂U : K₂ ⊆ U := subset_trans hK₂K₃ hK₃U
  -- the zeros of the limit on the two compacta
  have hA₃fin : (K₃ ∩ {z | G x₀ z = 0}).Finite :=
    finite_zeros_of_isCompact hU (hG x₀) hiso hK₃c hK₃U
  have hA₂fin : (K₂ ∩ {z | G x₀ z = 0}).Finite :=
    finite_zeros_of_isCompact hU (hG x₀) hiso hK₂c hK₂U
  set A₃ : Finset ℂ := hA₃fin.toFinset with hA₃def
  set A₂ : Finset ℂ := hA₂fin.toFinset with hA₂def
  have hA₂A₃ : ∀ a ∈ A₂, a ∈ A₃ := by
    intro a ha
    rw [hA₂def, Set.Finite.mem_toFinset] at ha
    rw [hA₃def, Set.Finite.mem_toFinset]
    exact ⟨hK₂K₃ ha.1, ha.2⟩
  set M : ℕ := ∑ a ∈ A₂, zeroMult (G x₀) a with hMdef
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro η hη
  set θ : ℝ := η / (2 * (M + 1)) with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  -- a radius on which the test function varies by at most `θ`, separating the zeros
  have hφK₃ : UniformContinuousOn φ K₃ := hK₃c.uniformContinuousOn_of_continuous hφ.continuousOn
  obtain ⟨δ₁, hδ₁, hφδ₁⟩ := Metric.uniformContinuousOn_iff.mp hφK₃ θ hθ
  obtain ⟨δ, hδ, hδρ, hsep⟩ := exists_separating_radius A₃ (ρ := min ρ₀ δ₁) (lt_min hρ₀ hδ₁)
  have hδρ₀ : 4 * δ ≤ ρ₀ := le_trans hδρ (min_le_left _ _)
  have hδδ₁ : 4 * δ ≤ δ₁ := le_trans hδρ (min_le_right _ _)
  -- the closed discs around the zeros stay inside the larger compactum
  have hballK₃ : ∀ a ∈ A₂, closedBall a (2 * δ) ⊆ K₃ := by
    intro a ha
    have haK₂ : a ∈ K₂ := by
      rw [hA₂def, Set.Finite.mem_toFinset] at ha
      exact ha.1
    refine subset_trans (closedBall_subset_cthickening haK₂ (2 * δ)) ?_
    refine subset_trans (cthickening_cthickening_subset (by positivity) (by positivity) K) ?_
    refine cthickening_mono ?_ K
    linarith
  have hballU : ∀ a ∈ A₂, closedBall a (2 * δ) ⊆ U := fun a ha =>
    subset_trans (hballK₃ a ha) hK₃U
  -- around each zero the local exchange applies
  have hloc : ∀ a : ℂ, ∃ ε : ℝ, 0 < ε ∧ (a ∈ A₂ →
      ∀ h : ℂ → ℂ, DifferentiableOn ℂ h U →
        (∀ z ∈ closedBall a (2 * δ), ‖h z - G x₀ z‖ ≤ ε) →
          ∃ Za : Finset ℂ, (∀ w ∈ Za, w ∈ ball a δ) ∧
            (∀ z ∈ ball a δ, h z = 0 ↔ z ∈ Za) ∧
            (∑ w ∈ Za, zeroMult h w) = zeroMult (G x₀) a) := by
    intro a
    by_cases ha : a ∈ A₂
    · have ha' := ha
      rw [hA₂def, Set.Finite.mem_toFinset] at ha'
      have honly : ∀ w ∈ closedBall a (2 * δ), G x₀ w = 0 → w = a := by
        intro w hw hw0
        by_contra hwa
        have hwA₃ : w ∈ A₃ := by
          rw [hA₃def, Set.Finite.mem_toFinset]
          exact ⟨hballK₃ a ha hw, hw0⟩
        have := hsep a (hA₂A₃ a ha) w hwA₃ (Ne.symm hwa)
        have hd : dist w a ≤ 2 * δ := mem_closedBall.mp hw
        rw [dist_comm] at hd
        linarith
      obtain ⟨ε, hε, hprop⟩ :=
        exists_local_zeroSet hU (hG x₀) hδ (hballU a ha) ha'.2 honly
      exact ⟨ε, hε, fun _ => hprop⟩
    · exact ⟨1, one_pos, fun hcon => absurd hcon ha⟩
  choose εf hεfpos hεfprop using hloc
  -- the compact remainder, where the limit does not vanish
  set W : Set ℂ := K₂ \ ⋃ a ∈ (A₂ : Set ℂ), ball a δ with hWdef
  have hWc : IsCompact W := hK₂c.diff (isOpen_biUnion fun a _ => isOpen_ball)
  have hWK₂ : W ⊆ K₂ := Set.sdiff_subset
  have hWne : ∀ z ∈ W, G x₀ z ≠ 0 := by
    intro z hz h0
    have hzA : z ∈ (A₂ : Set ℂ) := by
      rw [Finset.mem_coe, hA₂def, Set.Finite.mem_toFinset]
      exact ⟨hz.1, h0⟩
    exact hz.2 (mem_biUnion hzA (mem_ball_self hδ))
  obtain ⟨c₀, hc₀pos, hc₀⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z ∈ W, c₀ ≤ ‖G x₀ z‖ := by
    rcases W.eq_empty_or_nonempty with hWe | hWn
    · refine ⟨1, one_pos, fun z hz => ?_⟩
      rw [hWe] at hz
      exact absurd hz (by simp)
    · obtain ⟨w, hw, hmin⟩ := hWc.exists_isMinOn hWn
        (((hG x₀).mono (subset_trans hWK₂ hK₂U)).continuousOn.norm)
      exact ⟨‖G x₀ w‖, norm_pos_iff.mpr (hWne w hw), fun z hz => hmin hz⟩
  -- one radius of closeness for everything
  set E : Finset ℝ := insert (c₀ / 2) (A₂.image εf) with hEdef
  have hEne : E.Nonempty := ⟨c₀ / 2, Finset.mem_insert_self _ _⟩
  set ε : ℝ := E.min' hEne with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]; positivity
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hεfpos a
  have hεc₀ : ε ≤ c₀ / 2 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hεa : ∀ a ∈ A₂, ε ≤ εf a := fun a ha =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha))
  filter_upwards [hunif ε hεpos] with x hx
  -- the perturbation has no zeros on the remainder
  have hxW : ∀ z ∈ W, G x z ≠ 0 := by
    intro z hz h0
    have h1 : ‖G x z - G x₀ z‖ ≤ ε := hx z (hK₂U (hWK₂ hz))
    rw [h0, zero_sub, norm_neg] at h1
    have h2 := hc₀ z hz
    linarith
  -- the local zero sets of the perturbation
  have hlocx : ∀ a : ℂ, ∃ Za : Finset ℂ, a ∈ A₂ →
      ((∀ w ∈ Za, w ∈ ball a δ) ∧ (∀ z ∈ ball a δ, G x z = 0 ↔ z ∈ Za) ∧
        (∑ w ∈ Za, zeroMult (G x) w) = zeroMult (G x₀) a) := by
    intro a
    by_cases ha : a ∈ A₂
    · obtain ⟨Za, h1, h2, h3⟩ := hεfprop a ha (G x) (hG x) fun z hz =>
        le_trans (hx z (hballU a ha hz)) (hεa a ha)
      exact ⟨Za, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun hcon => absurd hcon ha⟩
  choose Za hZa using hlocx
  -- both pairings as finite sums
  have hsum₀ : divisorPairing (G x₀) φ = ∑ a ∈ A₂, (zeroMult (G x₀) a : ℂ) * φ a := by
    refine divisorPairing_eq_sum fun a hm hφa => ?_
    rw [hA₂def, Set.Finite.mem_toFinset]
    exact ⟨hKK₂ (subset_tsupport φ hφa), eq_zero_of_zeroMult_ne_zero hm⟩
  have hsumx : divisorPairing (G x) φ
      = ∑ w ∈ A₂.biUnion Za, (zeroMult (G x) w : ℂ) * φ w := by
    refine divisorPairing_eq_sum fun b hm hφb => ?_
    have hbK : b ∈ K := subset_tsupport φ hφb
    have hb0 : G x b = 0 := eq_zero_of_zeroMult_ne_zero hm
    have hbmem : b ∈ ⋃ a ∈ (A₂ : Set ℂ), ball a δ := by
      by_contra hcon
      exact hxW b ⟨hKK₂ hbK, hcon⟩ hb0
    obtain ⟨a, ha, hba⟩ := mem_iUnion₂.mp hbmem
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_coe.mp ha, ?_⟩
    exact ((hZa a (Finset.mem_coe.mp ha)).2.1 b hba).mp hb0
  -- the local zero sets are disjoint
  have hdisj : (A₂ : Set ℂ).PairwiseDisjoint Za := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr fun w hwa hwb => ?_
    have h1 : w ∈ ball a δ := (hZa a (Finset.mem_coe.mp ha)).1 w hwa
    have h2 : w ∈ ball b δ := (hZa b (Finset.mem_coe.mp hb)).1 w hwb
    have h3 : dist a b ≤ dist a w + dist w b := dist_triangle a w b
    rw [dist_comm a w] at h3
    have h4 := hsep a (hA₂A₃ a (Finset.mem_coe.mp ha)) b (hA₂A₃ b (Finset.mem_coe.mp hb)) hab
    have h5 : dist w a < δ := mem_ball.mp h1
    have h6 : dist w b < δ := mem_ball.mp h2
    linarith
  rw [hsumx, hsum₀, Finset.sum_biUnion hdisj, dist_eq_norm, ← Finset.sum_sub_distrib]
  -- the termwise estimate
  have hterm : ∀ a ∈ A₂,
      ‖(∑ w ∈ Za a, (zeroMult (G x) w : ℂ) * φ w) - (zeroMult (G x₀) a : ℂ) * φ a‖
        ≤ (zeroMult (G x₀) a : ℝ) * θ := by
    intro a ha
    obtain ⟨hball', hzero', hsum'⟩ := hZa a ha
    have haK₃ : a ∈ K₃ := hK₂K₃ (by
      rw [hA₂def, Set.Finite.mem_toFinset] at ha
      exact ha.1)
    have hrw : (∑ w ∈ Za a, (zeroMult (G x) w : ℂ) * φ w) - (zeroMult (G x₀) a : ℂ) * φ a
        = ∑ w ∈ Za a, (zeroMult (G x) w : ℂ) * (φ w - φ a) := by
      have h1 : ∑ w ∈ Za a, (zeroMult (G x) w : ℂ) * (φ w - φ a)
          = (∑ w ∈ Za a, (zeroMult (G x) w : ℂ) * φ w)
            - (∑ w ∈ Za a, (zeroMult (G x) w : ℂ)) * φ a := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [h1, ← Nat.cast_sum, hsum']
    rw [hrw]
    refine le_trans (norm_sum_le _ _) ?_
    have hbound : ∀ w ∈ Za a, ‖(zeroMult (G x) w : ℂ) * (φ w - φ a)‖
        ≤ (zeroMult (G x) w : ℝ) * θ := by
      intro w hw
      rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hwball : w ∈ ball a δ := hball' w hw
      have hwK₃ : w ∈ K₃ := hballK₃ a ha (by
        rw [mem_closedBall]
        exact le_of_lt (lt_of_lt_of_le (mem_ball.mp hwball) (by linarith)))
      have hd : dist w a < δ₁ := lt_of_lt_of_le (mem_ball.mp hwball) (by linarith)
      have := hφδ₁ w hwK₃ a haK₃ hd
      rw [Complex.dist_eq] at this
      exact this.le
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [← Finset.sum_mul, ← Nat.cast_sum, hsum']
  refine lt_of_le_of_lt (le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)) ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum, ← hMdef, hθdef]
  rw [div_eq_mul_inv, ← mul_assoc]
  rw [mul_comm (M : ℝ) η, mul_assoc]
  refine lt_of_le_of_lt (le_of_eq rfl) ?_
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hfrac : (M : ℝ) * (2 * ((M : ℝ) + 1))⁻¹ < 1 := by
    rw [inv_eq_one_div, mul_one_div, div_lt_one (by positivity)]
    linarith
  calc η * ((M : ℝ) * (2 * ((M : ℝ) + 1))⁻¹) < η * 1 :=
        mul_lt_mul_of_pos_left hfrac hη
    _ = η := mul_one η

/-- The pairing only sees the function near the support of the test function. -/
theorem divisorPairing_congr {V : Set ℂ} (hV : IsOpen V) {f g φ : ℂ → ℂ}
    (hfg : Set.EqOn f g V) (hsupp : tsupport φ ⊆ V) :
    divisorPairing f φ = divisorPairing g φ := by
  refine finsum_congr fun a => ?_
  by_cases ha : φ a = 0
  · rw [ha, mul_zero, mul_zero]
  · have haV : a ∈ V := hsupp (subset_tsupport φ ha)
    have hev : f =ᶠ[nhds a] g := Filter.eventuallyEq_of_mem (hV.mem_nhds haV) hfg
    rw [zeroMult, zeroMult, analyticOrderAt_congr hev]

end GaloisForLFunctions.HTGeometry
