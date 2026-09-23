import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCofinalScheduleNoGo

/-!
# Counterterm necessity for squarefree-half regularizations

Any correction that makes a cofinal Cayley--Dirichlet family locally bounded must itself be
unbounded at the fixed exterior point.  In particular, pointwise-vanishing or uniformly bounded
perturbations cannot repair the raw truncations.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A counterterm-corrected Cayley--Dirichlet approximation. -/
def poleClearedFirstTraceCountertermScheduledApprox
    (counterterm : ℕ → ℂ → ℂ) (kappa : ℕ → ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox (kappa N) s *
      (squarefreeHalfDirichletPartialSum N s + counterterm N s) /
    squarefreeCarlemanHalfDet s

/-- Local boundedness of a counterterm-corrected scheduled family. -/
def PoleClearedFirstTraceCountertermScheduledLocallyBounded
    (counterterm : ℕ → ℂ → ℂ) (kappa : ℕ → ℕ) : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N w‖ ≤ C

/-- Source-faithful counterterms are analytic on `rightHalf` and disappear compact-open in the
Euler chamber. -/
def SquarefreeHalfCountertermAdmissible (counterterm : ℕ → ℂ → ℂ) : Prop :=
  (∀ N, AnalyticOnNhd ℂ (counterterm N) rightHalf) ∧
    TendstoLocallyUniformlyOn counterterm (fun _ => 0) atTop farHalf

private theorem counterterm_tendstoLocallyUniformlyOn_comp_index
    {ι κ α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f p s) {k : κ → ι} (hk : Tendsto k q p) :
    TendstoLocallyUniformlyOn (fun n => F (k n)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, hF⟩ := hF u hu x hx
  exact ⟨t, ht, hk.eventually hF⟩

private theorem counterterm_tendstoLocallyUniformlyOn_const
    {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {p : Filter ι} {s : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ι => g) g p s := by
  intro u hu x hx
  exact ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

/-- Admissible counterterms preserve holomorphy of every corrected approximant. -/
theorem analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
    {counterterm : ℕ → ℂ → ℂ} (hadm : SquarefreeHalfCountertermAdmissible counterterm)
    (kappa : ℕ → ℕ) (N : ℕ) :
    AnalyticOnNhd ℂ
      (poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N) rightHalf := by
  exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N)).mul
    (((analyticOnNhd_squarefreeHalfDirichletPartialSum N).mono (Set.subset_univ _)).add
      (hadm.1 N)) |>.div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)

/-- Admissible counterterms preserve the source limit in the Euler chamber. -/
theorem tendstoLocallyUniformlyOn_poleClearedFirstTraceCountertermScheduledApprox
    {counterterm : ℕ → ℂ → ℂ} (hadm : SquarefreeHalfCountertermAdmissible counterterm)
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    TendstoLocallyUniformlyOn
      (poleClearedFirstTraceCountertermScheduledApprox counterterm kappa)
      poleClearedFirstTraceSourceLimit atTop farHalf := by
  have hr := counterterm_tendstoLocallyUniformlyOn_comp_index
    tendstoLocallyUniformlyOn_poleFactorSqrtApprox hkappa
  have hrcont : ContinuousOn poleFactorSqrtCayleyLimit farHalf :=
    hr.continuousOn (Frequently.of_forall fun n =>
      (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa n)).continuousOn.mono
        farHalf_subset_rightHalf)
  have hzero : ContinuousOn (fun _ : ℂ => (0 : ℂ)) farHalf := continuousOn_const
  have hnum := hr.mul₀ hadm.2 hrcont hzero
  have hden : TendstoLocallyUniformlyOn
      (fun _ : ℕ => squarefreeCarlemanHalfDet) squarefreeCarlemanHalfDet atTop farHalf :=
    counterterm_tendstoLocallyUniformlyOn_const squarefreeCarlemanHalfDet
  have hdencont : ContinuousOn squarefreeCarlemanHalfDet farHalf :=
    analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf.continuousOn.mono
      farHalf_subset_rightHalf
  have hcorr := hnum.div₀ hden (hrcont.mul hzero) hdencont
    (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)
  have hcorr' : TendstoLocallyUniformlyOn
      (fun N s => poleFactorSqrtApprox (kappa N) s * counterterm N s /
        squarefreeCarlemanHalfDet s) (fun _ => 0) atTop farHalf := by
    convert hcorr using 1
    · rfl
    · ext s
      simp
  have hsum :=
    (tendstoLocallyUniformlyOn_poleClearedFirstTraceScheduledApprox hkappa).add hcorr'
  convert hsum using 1
  · ext N s
    simp only [Pi.add_apply]
    rw [poleClearedFirstTraceCountertermScheduledApprox,
      poleClearedFirstTraceScheduledApprox]
    ring
  · ext s
    simp

/-- A source-faithful locally bounded corrected family proves the first RH rung. -/
theorem rhLadder_one_of_countertermScheduledLocallyBounded
    {counterterm : ℕ → ℂ → ℂ} (hadm : SquarefreeHalfCountertermAdmissible counterterm)
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    RHLadder 1 := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N =>
        (analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
          hadm kappa N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        (tendstoLocallyUniformlyOn_poleClearedFirstTraceCountertermScheduledApprox
          hadm hkappa).tendsto_at hs⟩)
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  refine ⟨G, hGdiff.analyticOnNhd isOpen_rightHalf, ?_⟩
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      ((tendstoLocallyUniformlyOn_poleClearedFirstTraceCountertermScheduledApprox
        hadm hkappa).tendsto_at hs)
  let H : ℂ → ℂ := fun s => G s ^ (2 : ℕ) - poleClearedFirstTraceExponentialContinuation s
  have hHana : AnalyticOnNhd ℂ H rightHalf :=
    ((hGdiff.analyticOnNhd isOpen_rightHalf).pow 2).sub
      analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hmem : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf := isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero' : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 := hmem.mono fun s hs => by
      dsimp [H]
      rw [hGeq hs, poleClearedFirstTraceSourceLimit_sq hs, sub_self]
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero').frequently
  have hHall := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_rightHalf.isPreconnected (farHalf_subset_rightHalf two_mem_farHalf) hfreq
  intro s hs
  have hzero' := hHall hs
  change G s ^ (2 : ℕ) - poleClearedFirstTraceExponentialContinuation s = 0 at hzero'
  exact sub_eq_zero.mp hzero'

/-- If the corrected arithmetic values have a bounded tail, the correction cannot also have one. -/
theorem counterterm_not_eventually_bounded_of_corrected_eventually_bounded
    {counterterm : ℕ → ℂ}
    (hcorrected : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint + counterterm N‖ ≤ C) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N → ‖counterterm N‖ ≤ B := by
  obtain ⟨C, N₀, hC⟩ := hcorrected
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
  refine ⟨C + B, max N₀ M₀, fun N hN => ?_⟩
  have hNC : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNB : M₀ ≤ N := le_trans (le_max_right _ _) hN
  calc
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ =
        ‖(squarefreeHalfDirichletPartialSum N boundaryExteriorPoint + counterterm N) -
          counterterm N‖ := by ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint + counterterm N‖ +
          ‖counterterm N‖ := norm_sub_le _ _
    _ ≤ C + B := add_le_add (hC N hNC) (hB N hNB)

/-- Every locally bounded cofinal corrected family pays an unbounded counterterm at `s = 6/11`. -/
theorem counterterm_not_eventually_bounded_of_cofinal_locallyBounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N boundaryExteriorPoint‖ ≤ B := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N
        boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 24))
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  apply counterterm_not_eventually_bounded_of_corrected_eventually_bounded
  refine ⟨K, N₀, fun N hN => ?_⟩
  have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow (hN₀ N hN)
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
            counterterm N boundaryExteriorPoint‖ ≤ K := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hone : (1 : ℝ) ≤ (5 : ℝ) ^ (kappa N - 24) := one_le_pow₀ (by norm_num)
  calc
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
        counterterm N boundaryExteriorPoint‖ =
        1 * ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
          counterterm N boundaryExteriorPoint‖ := by ring
    _ ≤ (5 : ℝ) ^ (kappa N - 24) *
        ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
          counterterm N boundaryExteriorPoint‖ :=
      mul_le_mul_of_nonneg_right hone (norm_nonneg _)
    _ ≤ ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
        ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
          counterterm N boundaryExteriorPoint‖ :=
      mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ ≤ K := hprod

/-- An eventually bounded correction cannot repair any cofinal raw schedule. -/
theorem no_cofinal_locallyBounded_of_counterterm_eventually_bounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm : ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N boundaryExteriorPoint‖ ≤ B) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  exact (counterterm_not_eventually_bounded_of_cofinal_locallyBounded hkappa hloc)
    hcounterterm

/-- A correction tending to zero at the exterior point cannot repair any cofinal raw schedule. -/
theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm : Tendsto (fun N => counterterm N boundaryExteriorPoint) atTop (𝓝 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  apply no_cofinal_locallyBounded_of_counterterm_eventually_bounded hkappa
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

end

end RHTower
