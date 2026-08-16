import GaloisForLFunctions.Bottcher.MontelNormal
import GaloisForLFunctions.HTGeometry.PositiveRealPartRigidity
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Vitali's convergence theorem

A uniformly bounded family of holomorphic functions that converges pointwise on a set with an
accumulation point converges locally uniformly on the whole disc.

The proof is Montel plus the identity theorem, assembled through the criterion that a sequence
converges once every subsequence has a further subsequence converging to the *same* limit.  Montel
supplies the subsequential limits; the pointwise hypothesis pins them down on the uniqueness set;
and the identity theorem propagates that agreement to the whole disc.  No diagonal extraction and
no explicit `ε`-`N` bookkeeping is needed.

This is the upgrade a normal family needs before a limit computed on one curve can be treated as
the limit of the family.
-/

open Complex Metric Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A sequence of continuous functions converges uniformly on a compact ball as soon as every
subsequence has a further subsequence converging uniformly there to the same limit. -/
theorem tendstoUniformlyOn_closedBall_of_forall_subseq
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {c : ℂ} {s : ℝ}
    (hGc : ContinuousOn G (closedBall c s))
    (hFc : ∀ n, ContinuousOn (F n) (closedBall c s))
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, TendstoUniformlyOn (fun k => F (ns (ms k))) G atTop (closedBall c s)) :
    TendstoUniformlyOn F G atTop (closedBall c s) := by
  classical
  haveI hcs : CompactSpace ↥(closedBall c s) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall c s)
  let bcf : ℕ → ↥(closedBall c s) →ᵇ ℂ :=
    fun n => mkOfCompact ⟨(closedBall c s).restrict (F n), (hFc n).restrict⟩
  let bcfG : ↥(closedBall c s) →ᵇ ℂ :=
    mkOfCompact ⟨(closedBall c s).restrict G, hGc.restrict⟩
  have hbcf : ∀ n (x : ↥(closedBall c s)), bcf n x = F n (x : ℂ) := fun _ _ => rfl
  have hbcfG : ∀ x : ↥(closedBall c s), bcfG x = G (x : ℂ) := fun _ => rfl
  have hmain : Tendsto bcf atTop (𝓝 bcfG) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, hms⟩ := h ns hns
    refine ⟨ms, ?_⟩
    rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
    have := (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mp hms
    exact this
  have hunif := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).mp hmain
  exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mpr hunif

/-- **Vitali's convergence theorem.**  A uniformly bounded holomorphic family with a pointwise
limit on a set accumulating at an interior point converges locally uniformly, and the limit is
holomorphic. -/
theorem vitali_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {c : ℂ} {R C r : ℝ} {z₀ : ℂ} {Y : Set ℂ}
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (ball c R))
    (hbd : ∀ n, ∀ z ∈ ball c R, ‖F n z‖ ≤ C)
    (hYsub : Y ⊆ ball c r) (hz₀ : z₀ ∈ ball c r)
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hconv : ∀ z ∈ Y, ∃ Lz : ℂ, Tendsto (fun n => F n z) atTop (𝓝 Lz)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball c r) ∧
      TendstoLocallyUniformlyOn F G atTop (ball c r) := by
  classical
  choose L hL using hconv
  obtain ⟨φ₀, G, hφ₀, hG_unif, hG_diff⟩ := Bottcher.montel_subseq hr0 hrR hF hbd
  have hGY : ∀ (z : ℂ) (hz : z ∈ Y), G z = L z hz := by
    intro z hz
    have h1 : Tendsto (fun k => F (φ₀ k) z) atTop (𝓝 (G z)) :=
      hG_unif.tendsto_at (ball_subset_closedBall (hYsub hz))
    have h2 : Tendsto (fun k => F (φ₀ k) z) atTop (𝓝 (L z hz)) :=
      (hL z hz).comp hφ₀.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  -- every subsequential Montel limit agrees with `G` on the whole disc
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, StrictMono ms ∧
        ∃ g : ℂ → ℂ, TendstoUniformlyOn (fun k => F (ns (ms k))) g atTop (closedBall c r) ∧
          EqOn g G (ball c r) := by
    intro ns hns
    obtain ⟨φ, g, hφ, hg_unif, hg_diff⟩ :=
      Bottcher.montel_subseq (F := fun k => F (ns k)) hr0 hrR (fun k => hF (ns k))
        (fun k => hbd (ns k))
    have hgY : ∀ (z : ℂ) (hz : z ∈ Y), g z = G z := by
      intro z hz
      have h1 : Tendsto (fun k => F (ns (φ k)) z) atTop (𝓝 (g z)) :=
        hg_unif.tendsto_at (ball_subset_closedBall (hYsub hz))
      have h2 : Tendsto (fun k => F (ns (φ k)) z) atTop (𝓝 (L z hz)) :=
        (hL z hz).comp (hns.comp hφ.tendsto_atTop)
      rw [hGY z hz]
      exact tendsto_nhds_unique h1 h2
    have hdiff : DifferentiableOn ℂ (fun z => g z - G z) (ball c r) := hg_diff.sub hG_diff
    have hana : AnalyticOnNhd ℂ (fun z => g z - G z) (ball c r) :=
      hdiff.analyticOnNhd isOpen_ball
    have hfreq : ∃ᶠ z in 𝓝[≠] z₀, (fun z => g z - G z) z = 0 := by
      refine hacc.mono fun z hz => ?_
      exact sub_eq_zero.mpr (hgY z hz)
    have heq : EqOn (fun z => g z - G z) 0 (ball c r) :=
      hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball c r).isPreconnected hz₀ hfreq
    refine ⟨φ, hφ, g, hg_unif, fun z hz => ?_⟩
    have := heq hz
    simpa [sub_eq_zero] using this
  refine ⟨G, hG_diff, ?_⟩
  -- uniform convergence on every strictly smaller closed ball
  have hsmall : ∀ s : ℝ, 0 < s → s < r →
      TendstoUniformlyOn F G atTop (closedBall c s) := by
    intro s hs0 hsr
    have hsubset : closedBall c s ⊆ ball c r := closedBall_subset_ball hsr
    have hGc : ContinuousOn G (closedBall c s) := (hG_diff.continuousOn).mono hsubset
    have hFc : ∀ n, ContinuousOn (F n) (closedBall c s) := fun n =>
      ((hF n).continuousOn).mono (hsubset.trans (ball_subset_ball (by linarith)))
    refine tendstoUniformlyOn_closedBall_of_forall_subseq hGc hFc ?_
    intro ns hns
    obtain ⟨ms, -, g, hg_unif, hgG⟩ := hsub ns hns
    refine ⟨ms, ?_⟩
    have hmono : TendstoUniformlyOn (fun k => F (ns (ms k))) g atTop (closedBall c s) :=
      hg_unif.mono (closedBall_subset_closedBall hsr.le)
    exact hmono.congr_right fun z hz => hgG (hsubset hz)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hKsub hK
  obtain ⟨s, hs0, hsr, hKs⟩ : ∃ s : ℝ, 0 < s ∧ s < r ∧ K ⊆ closedBall c s := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨r / 2, by linarith, by linarith, by simp [hemp]⟩
    · obtain ⟨w, hwK, hw⟩ :=
        hK.exists_isMaxOn hne (f := fun x : ℂ => dist x c)
          (continuous_id.dist continuous_const).continuousOn
      have hwr : dist w c < r := mem_ball.mp (hKsub hwK)
      have hw0 : (0 : ℝ) ≤ dist w c := dist_nonneg
      refine ⟨(dist w c + r) / 2, by linarith, by linarith, fun x hx => ?_⟩
      have hxle : dist x c ≤ dist w c := hw hx
      rw [mem_closedBall]
      linarith
  exact (hsmall s hs0 hsr).mono hKs

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Set Filter Topology

/-- **Vitali on an arbitrary domain.**  A locally bounded holomorphic family on a connected open
set, converging pointwise on a set that accumulates at one interior point, converges locally
uniformly on the whole set.  The set where pointwise convergence holds on a neighbourhood is open
by construction, nonempty by the disc form, and relatively closed because the disc form applies
again at every boundary point; connectedness closes the argument. -/
theorem vitali_tendstoLocallyUniformlyOn_of_isPreconnected
    {F : ℕ → ℂ → ℂ} {U Y : Set ℂ} {z₀ : ℂ}
    (hUc : IsPreconnected U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hloc : ∀ z ∈ U, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ ∃ C : ℝ,
      ∀ n, ∀ w ∈ ball z R, ‖F n w‖ ≤ C)
    (hz₀ : z₀ ∈ U) (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hconv : ∀ z ∈ Y, ∃ Lz : ℂ, Tendsto (fun n => F n z) atTop (𝓝 Lz)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ TendstoLocallyUniformlyOn F G atTop U := by
  classical
  set W : Set ℂ := {z | z ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧ ball z ε ⊆ U ∧
      ∀ w ∈ ball z ε, ∃ L : ℂ, Tendsto (fun n => F n w) atTop (𝓝 L)} with hWdef
  -- the disc form, applied at a point of `U` with a uniqueness set inside the third-radius ball
  have hdisc : ∀ z ∈ U, ∀ w : ℂ, ∀ Y' : Set ℂ,
      (∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ (∃ C : ℝ, ∀ n, ∀ v ∈ ball z R, ‖F n v‖ ≤ C) ∧
        Y' ⊆ ball z (R / 3) ∧ w ∈ ball z (R / 3) ∧ (∃ᶠ v in 𝓝[≠] w, v ∈ Y') ∧
        (∀ v ∈ Y', ∃ L : ℂ, Tendsto (fun n => F n v) atTop (𝓝 L))) →
      z ∈ W := by
    rintro z hzU w Y' ⟨R, hR, hballU, ⟨C, hC⟩, hY'sub, hwmem, hwacc, hY'conv⟩
    obtain ⟨G', hG'diff, hG'lim⟩ :=
      vitali_tendstoLocallyUniformlyOn (F := F) (c := z) (R := R) (C := C) (r := R / 3)
        (by linarith) (by linarith)
        (fun n => (hF n).mono hballU) hC hY'sub hwmem hwacc hY'conv
    refine ⟨hzU, R / 3, by linarith, ?_, ?_⟩
    · exact (ball_subset_ball (by linarith)).trans hballU
    · intro v hv
      exact ⟨G' v, hG'lim.tendsto_at hv⟩
  have hWopen : IsOpen W := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, ε, hε, hballU, hpt⟩
    refine ⟨ε / 2, by linarith, fun z' hz' => ?_⟩
    have hdz : dist z' z < ε / 2 := mem_ball.mp hz'
    have hsub : ball z' (ε / 2) ⊆ ball z ε := ball_subset_ball' (by linarith)
    exact ⟨hballU (hsub (mem_ball_self (by linarith))), ε / 2, by linarith,
      hsub.trans hballU, fun w hw => hpt w (hsub hw)⟩
  have hWne : (U ∩ W).Nonempty := by
    obtain ⟨R, hR, hballU, C, hC⟩ := hloc z₀ hz₀
    refine ⟨z₀, hz₀, hdisc z₀ hz₀ z₀ (Y ∩ ball z₀ (R / 3))
      ⟨R, hR, hballU, ⟨C, hC⟩, inter_subset_right, mem_ball_self (by linarith), ?_, ?_⟩⟩
    · refine hacc.and_eventually ?_
      exact nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ (by linarith))
    · exact fun v hv => hconv v hv.1
  have hWclosed : ∀ z ∈ U, z ∈ closure W → z ∈ W := by
    intro z hzU hzc
    obtain ⟨R, hR, hballU, C, hC⟩ := hloc z hzU
    obtain ⟨w, hwW, hzw⟩ : ∃ w ∈ W, dist z w < R / 6 :=
      Metric.mem_closure_iff.mp hzc (R / 6) (by linarith)
    have hwz : dist w z < R / 6 := by rwa [dist_comm]
    obtain ⟨-, δ, hδ, hδU, hδpt⟩ := hwW
    set δ' : ℝ := min δ (R / 6) with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
    have hsub : ball w δ' ⊆ ball z (R / 3) := by
      refine ball_subset_ball' ?_
      have : δ' ≤ R / 6 := min_le_right _ _
      linarith
    refine hdisc z hzU w (ball w δ') ⟨R, hR, hballU, ⟨C, hC⟩, hsub, ?_, ?_, ?_⟩
    · exact hsub (mem_ball_self hδ'0)
    · exact Filter.Eventually.frequently
        (nhdsWithin_le_nhds (Metric.ball_mem_nhds w hδ'0))
    · exact fun v hv => hδpt v (ball_subset_ball (min_le_left _ _) hv)
  have hUW : U ⊆ W := by
    have hcover : U ⊆ W ∪ (closure W)ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure W
      · exact Or.inl (hWclosed z hz hzc)
      · exact Or.inr hzc
    have hempty : U ∩ (closure W)ᶜ = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
      obtain ⟨y, hyU, hyW, hyc⟩ :=
        hUc W (closure W)ᶜ hWopen isClosed_closure.isOpen_compl hcover hWne ⟨x, hx⟩
      exact hyc (subset_closure hyW)
    intro z hz
    by_cases hzc : z ∈ closure W
    · exact hWclosed z hz hzc
    · exact absurd (Set.eq_empty_iff_forall_notMem.mp hempty z ⟨hz, hzc⟩) not_false
  have hptU : ∀ z ∈ U, ∃ L : ℂ, Tendsto (fun n => F n z) atTop (𝓝 L) := by
    intro z hz
    obtain ⟨-, ε, hε, -, hpt⟩ := hUW hz
    exact hpt z (mem_ball_self hε)
  set G : ℂ → ℂ := fun z => if hz : z ∈ U then (hptU z hz).choose else 0 with hGdef
  have hGlim : ∀ z ∈ U, Tendsto (fun n => F n z) atTop (𝓝 (G z)) := by
    intro z hz
    rw [hGdef]
    simp only [dif_pos hz]
    exact (hptU z hz).choose_spec
  -- locally uniform convergence around every point
  have hlocal : ∀ z ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball z ρ ⊆ U ∧
      TendstoLocallyUniformlyOn F G atTop (ball z ρ) := by
    intro z hz
    obtain ⟨R, hR, hballU, C, hC⟩ := hloc z hz
    have hY'sub : ball z (R / 6) ⊆ ball z (R / 3) := ball_subset_ball (by linarith)
    have hconv' : ∀ v ∈ ball z (R / 6), ∃ L : ℂ, Tendsto (fun n => F n v) atTop (𝓝 L) :=
      fun v hv => hptU v (hballU (ball_subset_ball (by linarith) hv))
    obtain ⟨G', hG'diff, hG'lim⟩ :=
      vitali_tendstoLocallyUniformlyOn (F := F) (c := z) (R := R) (C := C) (r := R / 3)
        (by linarith) (by linarith) (fun n => (hF n).mono hballU) hC hY'sub
        (mem_ball_self (by linarith))
        (Filter.Eventually.frequently
          (nhdsWithin_le_nhds (Metric.ball_mem_nhds z (by linarith : (0:ℝ) < R / 6))))
        hconv'
    refine ⟨R / 3, by linarith, (ball_subset_ball (by linarith)).trans hballU, ?_⟩
    refine hG'lim.congr_right fun v hv => ?_
    exact tendsto_nhds_unique (hG'lim.tendsto_at hv)
      (hGlim v (hballU (ball_subset_ball (by linarith : R / 3 ≤ R) hv)))
  have hGdiff : DifferentiableOn ℂ G U := by
    intro z hz
    obtain ⟨ρ, hρ, hρU, hρlim⟩ := hlocal z hz
    have hdiff : DifferentiableOn ℂ G (ball z ρ) :=
      hρlim.differentiableOn
        (Filter.Eventually.of_forall fun n => (hF n).mono hρU) isOpen_ball
    exact ((hdiff z (mem_ball_self hρ)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (mem_ball_self hρ))).differentiableWithinAt
  refine ⟨G, hGdiff, ?_⟩
  intro u hu z hz
  obtain ⟨ρ, hρ, hρU, hρlim⟩ := hlocal z hz
  obtain ⟨t, ht, hev⟩ := hρlim u hu z (mem_ball_self hρ)
  refine ⟨t, ?_, hev⟩
  have hball : ball z ρ ∈ 𝓝 z := Metric.ball_mem_nhds z hρ
  have hteq : 𝓝[ball z ρ] z = 𝓝 z := nhdsWithin_eq_nhds.mpr hball
  rw [hteq] at ht
  exact nhdsWithin_le_nhds ht

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Set Filter Topology

/-- **Identification of the Vitali limit.**  If the pointwise limit on the uniqueness set is the
restriction of a holomorphic function on the whole domain, the family converges locally uniformly
to that function. -/
theorem tendstoLocallyUniformlyOn_of_pointwise_on_uniquenessSet
    {F : ℕ → ℂ → ℂ} {T : ℂ → ℂ} {U Y : Set ℂ} {z₀ : ℂ}
    (hUopen : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hloc : ∀ z ∈ U, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ ∃ C : ℝ,
      ∀ n, ∀ w ∈ ball z R, ‖F n w‖ ≤ C)
    (hT : DifferentiableOn ℂ T U)
    (hYsub : Y ⊆ U) (hz₀ : z₀ ∈ U) (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hconv : ∀ z ∈ Y, Tendsto (fun n => F n z) atTop (𝓝 (T z))) :
    TendstoLocallyUniformlyOn F T atTop U := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected hUc hF hloc hz₀ hacc
      (fun z hz => ⟨T z, hconv z hz⟩)
  have hGT : ∀ z ∈ Y, G z = T z := fun z hz =>
    tendsto_nhds_unique (hGlim.tendsto_at (hYsub hz)) (hconv z hz)
  have hana : AnalyticOnNhd ℂ (fun z => G z - T z) U :=
    (hGdiff.sub hT).analyticOnNhd hUopen
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, (fun z => G z - T z) z = 0 :=
    hacc.mono fun z hz => sub_eq_zero.mpr (hGT z hz)
  have heq : EqOn (fun z => G z - T z) 0 U :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hfreq
  refine hGlim.congr_right fun z hz => ?_
  have := heq hz
  simpa [sub_eq_zero] using this

/-- **The Herglotz limit is zero-free.**  A locally uniform limit of functions with positive real
part, itself positive at one point, has no zero in the domain. -/
theorem ne_zero_of_tendstoLocallyUniformlyOn_re_pos
    {F : ℕ → ℂ → ℂ} {T : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F T atTop U)
    (hpos : ∀ n, ∀ z ∈ U, 0 ≤ (F n z).re)
    {z₁ : ℂ} (hz₁ : z₁ ∈ U) (hz₁pos : 0 < (T z₁).re) :
    ∀ z ∈ U, T z ≠ 0 := by
  intro z hz hzero
  have hre := re_pos_of_tendstoLocallyUniformlyOn hUopen hUc
    (Filter.Eventually.of_forall hF) hlim (Filter.Eventually.of_forall hpos) hz₁ hz₁pos z hz
  rw [hzero] at hre
  simp at hre

end GaloisForLFunctions.HTGeometry
