import GaloisForLFunctions.Bottcher.RelativeBranchFamily

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- **Green-modulus contradiction from a dense approach set.**  The modulus identity only has
to hold on a dense basin-side approach set `A`; continuity extends it to the whole ball. -/
theorem no_green_modulus_continuation_dense_approach {c z₀ : ℂ} {r : ℝ}
    {g : ℂ → ℂ} {A : Set ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r))
    (hz₀ : z₀ ∈ filledJulia c)
    (hAdense : ball z₀ r ⊆ closure (ball z₀ r ∩ A))
    (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hmodA : ∀ z ∈ ball z₀ r, z ∈ A → ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hAne : (ball z₀ r ∩ A).Nonempty) :
    False := by
  have hcN : ContinuousOn (fun w => ‖g w‖) (ball z₀ r) := hgan.continuousOn.norm
  have hcE : ContinuousOn (fun w => Real.exp (greenFunctionDyn c w)) (ball z₀ r) :=
    (Real.continuous_exp.comp (continuous_greenFunctionDyn c)).continuousOn
  have hmod_all : ∀ z ∈ ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz
    have hzcl : z ∈ closure (ball z₀ r ∩ A) := hAdense hz
    have hne : (𝓝[ball z₀ r ∩ A] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hzcl
    have hsub : ball z₀ r ∩ A ⊆ ball z₀ r := inter_subset_left
    have hf : Tendsto (fun w => ‖g w‖) (𝓝[ball z₀ r ∩ A] z) (𝓝 (‖g z‖)) :=
      (hcN z hz).mono hsub
    have hh0 : Tendsto (fun w => Real.exp (greenFunctionDyn c w)) (𝓝[ball z₀ r ∩ A] z)
        (𝓝 (Real.exp (greenFunctionDyn c z))) :=
      (hcE z hz).mono hsub
    have heqs : ∀ w ∈ ball z₀ r ∩ A, Real.exp (greenFunctionDyn c w) = ‖g w‖ :=
      fun w hw => (hmodA w hw.1 hw.2).symm
    have hh : Tendsto (fun w => ‖g w‖) (𝓝[ball z₀ r ∩ A] z)
        (𝓝 (Real.exp (greenFunctionDyn c z))) :=
      hh0.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqs)
    exact tendsto_nhds_unique hf hh
  exact no_green_modulus_continuation hr hgan hz₀ hmod_all
    (by
      rcases hAne with ⟨z, hzball, hzA⟩
      exact ⟨z, hzball, hAsub hzA⟩)

/-- **Analytic-coefficient natural-boundary contradiction along a dense approach set.**  The
relation branch only has to be selected along `A`; density plus the Green-modulus identity still
forces an impossible analytic continuation. -/
theorem false_of_basin_branch_dendrite_analytic_denseApproach
    {c z₀ w₀ d : ℂ} {r : ℝ} {s : Finset ℕ} {a : ℕ → ℂ → ℂ}
    {A : Set ℂ}
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hAdense : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      ball z₀ ρ ⊆ closure (ball z₀ ρ ∩ A))
    (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (ball z₀ ρ ∩ A).Nonempty)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {β : ℂ → ℂ}
    (hβlim : Tendsto β (𝓝[A] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[A] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ᶠ z in 𝓝[A] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic ha hroot hpartial hd
  have hacont : ∀ i ∈ s, ContinuousAt (a i) z₀ := fun i hi => (ha i hi).continuousAt
  have hmatch : ∀ᶠ z in 𝓝[A] z₀, g z = β z :=
    branch_unique_within_analytic hacont hpartial hd hgAt.continuousAt hgz₀ hβlim
      (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
  have hgmod : ∀ᶠ z in 𝓝[A] z₀, ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    filter_upwards [hmatch, hβmod] with z hz hzm
    rw [hz, hzm]
  obtain ⟨ε₁, hε₁, hgan1⟩ := Metric.eventually_nhds_iff.mp hgAt.eventually_analyticAt
  obtain ⟨O, hOopen, hz₀O, hOsub⟩ := mem_nhdsWithin.mp hgmod
  obtain ⟨ε₂, hε₂, hOball⟩ := Metric.isOpen_iff.mp hOopen z₀ hz₀O
  set r' := min r (min ε₁ ε₂) with hr'def
  have hr' : 0 < r' := lt_min hr (lt_min hε₁ hε₂)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'1 : r' ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr'2 : r' ≤ ε₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine no_green_modulus_continuation_dense_approach (c := c) (z₀ := z₀) (g := g)
    (A := A) hr' ?_ hz₀ (hAdense r' hr' hr'r) hAsub ?_ (hAne r' hr' hr'r)
  · intro z hz
    exact hgan1 (lt_of_lt_of_le (mem_ball.mp hz) hr'1)
  · intro z hzball hzA
    exact hOsub ⟨hOball (Metric.ball_subset_ball hr'2 hzball), hzA⟩

/-- **Boundary limit along a chosen preconnected approach set.**  This is the `dendrite_branch_limit`
step without rewriting the approach filter to the full basin filter. -/
theorem dendrite_branch_limit_analytic_within {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    {z₀ : ℂ} {r : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hr : 0 < r)
    (hsepf : (fibrePoly a s z₀).Separable)
    (w : Fin N → ℂ → ℂ)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.ball z₀ r))
    (hwsep : ∀ z ∈ Metric.ball z₀ r, ∀ k l, k ≠ l → w k z ≠ w l z)
    (hwdeg : ∀ z ∈ Metric.ball z₀ r, (fibrePoly a s z).natDegree = N)
    (hwrel : ∀ k, ∀ z ∈ Metric.ball z₀ r, ∑ i ∈ s, a i z * (w k z) ^ i = 0)
    {A : Set ℂ} {β : ℂ → ℂ}
    (hAball : A ⊆ Metric.ball z₀ r)
    (hApre : IsPreconnected A)
    (hβc : ContinuousOn β A)
    (hβrel : ∀ z ∈ A, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ A) :
    ∃ (w₀ d : ℂ),
      (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
      HasDerivAt (fun y => ∑ i ∈ s, a i z₀ * y ^ i) d w₀ ∧ d ≠ 0 ∧
      Tendsto β (𝓝[A] z₀) (𝓝 w₀) := by
  have hwcA : ∀ k, ContinuousOn (w k) A := fun k => (hwc k).mono hAball
  have hwsepA : ∀ z ∈ A, ∀ k l, k ≠ l → w k z ≠ w l z :=
    fun z hz => hwsep z (hAball hz)
  have hwdegA : ∀ z ∈ A, (fibrePoly a s z).natDegree = N :=
    fun z hz => hwdeg z (hAball hz)
  have hwrelA : ∀ k, ∀ z ∈ A, ∑ i ∈ s, a i z * (w k z) ^ i = 0 :=
    fun k z hz => hwrel k z (hAball hz)
  obtain ⟨k, hk⟩ :=
    eqOn_branch_of_relation_analytic hN1 w β hApre hwcA hβc hwsepA hwdegA hwrelA hβrel hz₁
  have hwkAt : ContinuousAt (w k) z₀ := (hwc k).continuousAt (Metric.ball_mem_nhds z₀ hr)
  have hz₀ball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hroot : ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0 := hwrel k z₀ hz₀ball
  have hrootQ : (fibrePoly a s z₀).eval (w k z₀) = 0 := by
    rw [eval_fibrePoly]
    exact hroot
  have hd : (fibrePoly a s z₀).derivative.eval (w k z₀) ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsepf hrootQ
  have hpart := relation_hasDerivAt_w_analytic a s z₀ (w k z₀)
  have htend : Tendsto β (𝓝[A] z₀) (𝓝 (w k z₀)) := tendsto_within_of_eqOn hwkAt hk
  exact ⟨w k z₀, (fibrePoly a s z₀).derivative.eval (w k z₀), hroot, hpart, hd, htend⟩

/-- **Relative dendrite obstruction from a dense preconnected approach model.**  Replaces the
old full punctured-basin preconnectedness input by a dense approach family `A`: below every small
radius, `ball z₀ ρ ∩ A` is preconnected, nonempty, dense in the ball, and lies in the basin. -/
theorem false_of_global_basin_branch_analytic_denseApproach
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {r : ℝ} {A : Set ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    {β : ℂ → ℂ}
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hApre : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → IsPreconnected (Metric.ball z₀ ρ ∩ A))
    (hAdense : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ A))
    (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (Metric.ball z₀ ρ ∩ A).Nonempty)
    (hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c)ᶜ))
    (hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ,
        ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  obtain ⟨rBranch, w, hrBranch, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ₀ : ℝ := min r rBranch with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min hr hrBranch
  have hρ₀r : ρ₀ ≤ r := min_le_left _ _
  have hρ₀Branch : ρ₀ ≤ rBranch := min_le_right _ _
  let Approach : Set ℂ := Metric.ball z₀ ρ₀ ∩ A
  have hApproachBallBranch : Approach ⊆ Metric.ball z₀ rBranch := by
    intro z hz
    exact Metric.ball_subset_ball hρ₀Branch hz.1
  have hApproachBasin : Approach ⊆ (filledJulia c)ᶜ := by
    intro z hz
    exact hAsub hz.2
  have hApproachPre : IsPreconnected Approach := hApre ρ₀ hρ₀ hρ₀r
  have hβcA : ContinuousOn β Approach := by
    apply hβc.mono
    intro z hz
    exact ⟨Metric.ball_subset_ball hρ₀r hz.1, hApproachBasin hz⟩
  have hβrelA : ∀ z ∈ Approach, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    exact hβrel z ⟨Metric.ball_subset_ball hρ₀r hz.1, hApproachBasin hz⟩
  obtain ⟨z₁, hz₁⟩ := hAne ρ₀ hρ₀ hρ₀r
  obtain ⟨w₀, d, hroot, hpart, hd, htend⟩ :=
    dendrite_branch_limit_analytic_within hN1 hrBranch hsep w hwc hwsep hwdeg hwrel
      hApproachBallBranch hApproachPre hβcA hβrelA hz₁
  have hrelFilt : ∀ᶠ z in 𝓝[Approach] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrelA
  have hmodFilt : ∀ᶠ z in 𝓝[Approach] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z) :=
    Filter.eventually_of_mem self_mem_nhdsWithin (by
      intro z hz
      exact hβmod z ⟨Metric.ball_subset_ball hρ₀r hz.1, hApproachBasin hz⟩)
  refine false_of_basin_branch_dendrite_analytic_denseApproach
    (c := c) (z₀ := z₀) (w₀ := w₀) (d := d) (r := ρ₀) (A := Approach)
    ha hρ₀ hz₀ ?_ hApproachBasin ?_ hroot hpart hd htend hrelFilt hmodFilt
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ Approach = Metric.ball z₀ ρ ∩ A := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact hAdense ρ hρ (le_trans hρle hρ₀r)
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ Approach = Metric.ball z₀ ρ ∩ A := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact hAne ρ hρ (le_trans hρle hρ₀r)

end Bottcher

namespace Bottcher

/-- A rotated translated slit sector has a point in every positive-radius tip ball. -/
theorem nonempty_ball_inter_rotated_translated_slitPlane (u z₀ : ℂ) (hu : ‖u‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane}).Nonempty := by
  let w : ℂ := ((ρ / 2 : ℝ) : ℂ)
  let center : ℂ := z₀ + u⁻¹ * w
  have hune : u ≠ 0 := by
    intro h
    have hnorm : ‖u‖ = 0 := by rw [h, norm_zero]
    rw [hu] at hnorm
    norm_num at hnorm
  have hw_pos : 0 < ρ / 2 := half_pos hρ
  have hw_slit : w ∈ Complex.slitPlane := by
    dsimp [w]
    exact Complex.ofReal_mem_slitPlane.2 hw_pos
  have hcenter_ball : center ∈ Metric.ball z₀ ρ := by
    dsimp [center, w]
    rw [Metric.mem_ball]
    simp only [dist_eq_norm, add_sub_cancel_left]
    rw [norm_mul, norm_inv, hu, inv_one, one_mul]
    have hnorm : ‖((ρ / 2 : ℝ) : ℂ)‖ = ρ / 2 :=
      Complex.norm_of_nonneg (le_of_lt hw_pos)
    rw [hnorm]
    exact half_lt_self hρ
  have hcenter_slit : u * (center - z₀) ∈ Complex.slitPlane := by
    dsimp [center]
    rw [add_sub_cancel_left]
    rw [← mul_assoc, mul_inv_cancel₀ hune, one_mul]
    exact hw_slit
  exact ⟨center, hcenter_ball, hcenter_slit⟩

/-- A local rotated-slit basin sector supplies the dense preconnected approach model.  This is the
piece needed to feed the dense-approach hRigid obstruction from an actual local-access geometry
source, without first proving full punctured-basin preconnectedness. -/
theorem false_of_global_basin_branch_analytic_rotatedSlitDenseApproach
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ u : ℂ}
    {rTip : ℝ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    {β : ℂ → ℂ}
    (hz₀ : z₀ ∈ filledJulia c)
    (hu : ‖u‖ = 1) (hrTip : 0 < rTip)
    (hslit : ∀ ρ, 0 < ρ → ρ ≤ rTip →
      Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
        Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ)
    (hβc : ContinuousOn β (Metric.ball z₀ rTip ∩ (filledJulia c)ᶜ))
    (hβrel : ∀ z ∈ Metric.ball z₀ rTip ∩ (filledJulia c)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ z ∈ Metric.ball z₀ rTip ∩ (filledJulia c)ᶜ,
        ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  let A : Set ℂ := Metric.ball z₀ rTip ∩ {z | u * (z - z₀) ∈ Complex.slitPlane}
  have hAsub : A ⊆ (filledJulia c)ᶜ := by
    intro z hz
    exact (hslit rTip hrTip le_rfl hz).2
  refine false_of_global_basin_branch_analytic_denseApproach
    (c := c) (z₀ := z₀) (r := rTip) (A := A)
    hsupp hN hN1 ha hlead hsep hrTip hz₀ ?_ ?_ hAsub ?_ hβc hβrel hβmod
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ A =
        Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact isPreconnected_ball_inter_rotated_translated_slitPlane u z₀ hu hρ
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ A =
        Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact ball_subset_closure_ball_inter_rotated_translated_slitPlane u z₀ hu
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ A =
        Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact nonempty_ball_inter_rotated_translated_slitPlane u z₀ hu hρ

end Bottcher

namespace Bottcher

/-- **Relative dendrite obstruction from relation data only on the dense approach.**  This is the
`false_of_global_basin_branch_analytic_denseApproach` argument with the relation and modulus hypotheses
restricted to `ball z₀ r ∩ A`; the approach itself supplies the preconnected branch-selection path and
the dense Green-modulus contradiction. -/
theorem false_of_global_basin_branch_analytic_denseApproach_on
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {r : ℝ} {A : Set ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    {β : ℂ → ℂ}
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hApre : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → IsPreconnected (Metric.ball z₀ ρ ∩ A))
    (hAdense : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ A))
    (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (Metric.ball z₀ ρ ∩ A).Nonempty)
    (hβcA : ContinuousOn β (Metric.ball z₀ r ∩ A))
    (hβrelA : ∀ z ∈ Metric.ball z₀ r ∩ A, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmodA : ∀ z ∈ Metric.ball z₀ r ∩ A,
        ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  obtain ⟨rBranch, w, hrBranch, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ₀ : ℝ := min r rBranch with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min hr hrBranch
  have hρ₀r : ρ₀ ≤ r := min_le_left _ _
  have hρ₀Branch : ρ₀ ≤ rBranch := min_le_right _ _
  let Approach : Set ℂ := Metric.ball z₀ ρ₀ ∩ A
  have hApproachBallBranch : Approach ⊆ Metric.ball z₀ rBranch := by
    intro z hz
    exact Metric.ball_subset_ball hρ₀Branch hz.1
  have hApproachBasin : Approach ⊆ (filledJulia c)ᶜ := by
    intro z hz
    exact hAsub hz.2
  have hApproachPre : IsPreconnected Approach := hApre ρ₀ hρ₀ hρ₀r
  have hβcApproach : ContinuousOn β Approach := by
    refine hβcA.mono ?_
    intro z hz
    exact ⟨Metric.ball_subset_ball hρ₀r hz.1, hz.2⟩
  have hβrelApproach : ∀ z ∈ Approach, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    exact hβrelA z ⟨Metric.ball_subset_ball hρ₀r hz.1, hz.2⟩
  have hβmodApproach : ∀ z ∈ Approach, ‖β z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz
    exact hβmodA z ⟨Metric.ball_subset_ball hρ₀r hz.1, hz.2⟩
  obtain ⟨z₁, hz₁⟩ := hAne ρ₀ hρ₀ hρ₀r
  obtain ⟨w₀, d, hroot, hpart, hd, htend⟩ :=
    dendrite_branch_limit_analytic_within hN1 hrBranch hsep w hwc hwsep hwdeg hwrel
      hApproachBallBranch hApproachPre hβcApproach hβrelApproach hz₁
  have hrelFilt : ∀ᶠ z in 𝓝[Approach] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrelApproach
  have hmodFilt : ∀ᶠ z in 𝓝[Approach] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z) :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβmodApproach
  refine false_of_basin_branch_dendrite_analytic_denseApproach
    (c := c) (z₀ := z₀) (w₀ := w₀) (d := d) (r := ρ₀) (A := Approach)
    ha hρ₀ hz₀ ?_ hApproachBasin ?_ hroot hpart hd htend hrelFilt hmodFilt
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ Approach = Metric.ball z₀ ρ ∩ A := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact hAdense ρ hρ (le_trans hρle hρ₀r)
  · intro ρ hρ hρle
    have hball_eq : Metric.ball z₀ ρ ∩ Approach = Metric.ball z₀ ρ ∩ A := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
    rw [hball_eq]
    exact hAne ρ hρ (le_trans hρle hρ₀r)

end Bottcher

namespace Bottcher

open Metric Filter

/-- **Relative dendrite obstruction from a single-scale preconnected basis family.**  The
∀ρ-preconnectivity of the dense-approach model is needed at ONE scale only (the branch-following
step); this variant takes a shrinking family `T t` of preconnected approach sets with a
fat-margin clause supplying density and nonemptiness.  Exactly the shape the linearization
collapse produces at a repelling boundary fixed point. -/
theorem false_of_global_basin_branch_analytic_basisApproach
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {r : ℝ} {T : ℝ → Set ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    {β : ℂ → ℂ}
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : Metric.ball z₀ r ∩ interior (filledJulia c) = ∅)
    (hT_sub : ∀ t : ℝ, 0 < t → t ≤ r → T t ⊆ Metric.ball z₀ t ∩ (filledJulia c)ᶜ)
    (hT_pre : ∀ t : ℝ, 0 < t → t ≤ r → IsPreconnected (T t))
    (hT_fat : ∀ t : ℝ, 0 < t → t ≤ r →
      (filledJulia c)ᶜ ∩ Metric.ball z₀ (t/2) ⊆ T t)
    (hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c)ᶜ))
    (hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ,
        ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  obtain ⟨rBranch, w, hrBranch, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ₀ : ℝ := min r rBranch with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min hr hrBranch
  have hρ₀r : ρ₀ ≤ r := min_le_left _ _
  have hρ₀B : ρ₀ ≤ rBranch := min_le_right _ _
  set Approach := T ρ₀ with hAdef
  have hAsubfull := hT_sub ρ₀ hρ₀ hρ₀r
  have hABallBranch : Approach ⊆ Metric.ball z₀ rBranch := fun z hz =>
    Metric.ball_subset_ball hρ₀B (hAsubfull hz).1
  have hAbasin : Approach ⊆ (filledJulia c)ᶜ := fun z hz => (hAsubfull hz).2
  have hApre : IsPreconnected Approach := hT_pre ρ₀ hρ₀ hρ₀r
  have hAballr : Approach ⊆ Metric.ball z₀ r := fun z hz =>
    Metric.ball_subset_ball hρ₀r (hAsubfull hz).1
  have hβcA : ContinuousOn β Approach := hβc.mono (fun z hz => ⟨hAballr hz, hAbasin hz⟩)
  have hβrelA : ∀ z ∈ Approach, ∑ i ∈ s, a i z * (β z) ^ i = 0 := fun z hz =>
    hβrel z ⟨hAballr hz, hAbasin hz⟩
  have hz₀notint : z₀ ∉ interior (filledJulia c) := by
    intro hcon
    have h1 : z₀ ∈ Metric.ball z₀ r ∩ interior (filledJulia c) :=
      ⟨Metric.mem_ball_self hr, hcon⟩
    rw [hempty] at h1
    exact h1
  obtain ⟨z₁, hz₁ball, hz₁basin⟩ :=
    exists_mem_ball_compl_filledJulia_of_not_mem_interior hz₀notint (half_pos hρ₀)
  have hz₁A : z₁ ∈ Approach := hT_fat ρ₀ hρ₀ hρ₀r ⟨hz₁basin, hz₁ball⟩
  obtain ⟨w₀, d, hroot, hpart, hd, htend⟩ :=
    dendrite_branch_limit_analytic_within hN1 hrBranch hsep w hwc hwsep hwdeg hwrel
      hABallBranch hApre hβcA hβrelA hz₁A
  have hrelFilt : ∀ᶠ z in 𝓝[Approach] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrelA
  have hmodFilt : ∀ᶠ z in 𝓝[Approach] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z) :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz =>
      hβmod z ⟨hAballr hz, hAbasin hz⟩)
  refine false_of_basin_branch_dendrite_analytic_denseApproach
    (c := c) (z₀ := z₀) (w₀ := w₀) (d := d) (r := ρ₀ / 2) (A := Approach)
    ha (half_pos hρ₀) hz₀ ?_ hAbasin ?_ hroot hpart hd htend hrelFilt hmodFilt
  · intro ρ hρ hρle
    have hsubT : Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ ⊆ Metric.ball z₀ ρ ∩ Approach := by
      rintro z ⟨hz1, hz2⟩
      refine ⟨hz1, hT_fat ρ₀ hρ₀ hρ₀r ⟨hz2, ?_⟩⟩
      exact Metric.ball_subset_ball (by linarith) hz1
    have hemptyρ : Metric.ball z₀ ρ ∩ interior (filledJulia c) = ∅ := by
      apply Set.eq_empty_of_subset_empty
      rw [← hempty]
      apply Set.inter_subset_inter_left
      apply Metric.ball_subset_ball
      linarith
    have hdense := density_basin_of_empty_interior hemptyρ
    exact fun z hz => closure_mono hsubT (hdense hz)
  · intro ρ hρ hρle
    obtain ⟨z₂, hz₂ball, hz₂basin⟩ :=
      exists_mem_ball_compl_filledJulia_of_not_mem_interior hz₀notint
        (by linarith : (0:ℝ) < ρ/2)
    refine ⟨z₂, ⟨Metric.ball_subset_ball (by linarith) hz₂ball,
      hT_fat ρ₀ hρ₀ hρ₀r ⟨hz₂basin, ?_⟩⟩⟩
    exact Metric.ball_subset_ball (by linarith) hz₂ball

end Bottcher
