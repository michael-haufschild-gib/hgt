import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroCriterion

/-!
# Independently scheduled Cesàro source criterion

Diagonal synchronization of arithmetic cutoff and Cayley pole degree is impossible. This module
separates them. Every cofinal pole-degree schedule preserves the exact Euler half-germ, so local
boundedness of the independently scheduled Cesàro family still forces `RHLadder 1`.

This is an exact bridge, not a proof of local boundedness. Its point is to isolate slow cofinal
pole schedules that are not covered by the diagonal discrete-derivative obstruction.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Independently scheduled pole transport of the arithmetic Cesàro half sums. -/
def poleClearedFirstTraceCesaroScheduledApprox
    (kappa : ℕ → ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox (kappa N) s * squarefreeHalfCesaroSum N s /
    squarefreeCarlemanHalfDet s

private theorem tendstoLocallyUniformlyOn_comp_nat_index
    {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f atTop s)
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (kappa n)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hF⟩ := hF u hu x hx
  exact ⟨t, ht, hkappa.eventually hF⟩

private theorem tendstoLocallyUniformlyOn_const_nat_schedule
    {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {s : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => g) g atTop s := by
  intro u hu x hx
  exact ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

theorem analyticOnNhd_poleClearedFirstTraceCesaroScheduledApprox_rightHalf
    (kappa : ℕ → ℕ) (N : ℕ) :
    AnalyticOnNhd ℂ (poleClearedFirstTraceCesaroScheduledApprox kappa N) rightHalf := by
  exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N)).mul
    ((analyticOnNhd_squarefreeHalfCesaroSum N).mono (Set.subset_univ _)) |>.div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)

/-- Every cofinal pole schedule preserves the exact canonical half on the Euler chamber. -/
theorem tendstoLocallyUniformlyOn_poleClearedFirstTraceCesaroScheduledApprox
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    TendstoLocallyUniformlyOn (poleClearedFirstTraceCesaroScheduledApprox kappa)
      poleClearedFirstTraceSourceLimit atTop farHalf := by
  have hr := tendstoLocallyUniformlyOn_comp_nat_index
    tendstoLocallyUniformlyOn_poleFactorSqrtApprox hkappa
  have hrcont : ContinuousOn poleFactorSqrtCayleyLimit farHalf :=
    hr.continuousOn (Frequently.of_forall fun n =>
      (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa n)).continuousOn.mono
        farHalf_subset_rightHalf)
  have hLcont : ContinuousOn (LSeries squarefreeConvolutionHalf) farHalf :=
    analyticOnNhd_LSeries_squarefreeConvolutionHalf.continuousOn
  have hdencont : ContinuousOn squarefreeCarlemanHalfDet farHalf :=
    analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf.continuousOn.mono
      farHalf_subset_rightHalf
  have hnum := hr.mul₀
    tendstoLocallyUniformlyOn_squarefreeHalfCesaroSum hrcont hLcont
  have hden : TendstoLocallyUniformlyOn
      (fun _ : ℕ => squarefreeCarlemanHalfDet) squarefreeCarlemanHalfDet atTop farHalf :=
    tendstoLocallyUniformlyOn_const_nat_schedule squarefreeCarlemanHalfDet
  have hdiv := hnum.div₀ hden (hrcont.mul hLcont) hdencont
    (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)
  convert hdiv using 1
  · ext N s
    rfl
  · ext s
    rfl

/-- Local boundedness of an independently scheduled Cesàro source sequence. -/
def PoleClearedFirstTraceCesaroScheduledLocallyBounded (kappa : ℕ → ℕ) : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R,
      ‖poleClearedFirstTraceCesaroScheduledApprox kappa N w‖ ≤ C

/-- **[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]** Local boundedness for any cofinal independent
schedule forces the first multiplicity rung. -/
theorem rhLadder_one_of_poleClearedFirstTraceCesaroScheduledLocallyBounded
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCesaroScheduledLocallyBounded kappa) : RHLadder 1 := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N =>
        (analyticOnNhd_poleClearedFirstTraceCesaroScheduledApprox_rightHalf
          kappa N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        (tendstoLocallyUniformlyOn_poleClearedFirstTraceCesaroScheduledApprox
          hkappa).tendsto_at hs⟩)
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  refine ⟨G, hGdiff.analyticOnNhd isOpen_rightHalf, ?_⟩
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      ((tendstoLocallyUniformlyOn_poleClearedFirstTraceCesaroScheduledApprox
        hkappa).tendsto_at hs)
  let H : ℂ → ℂ := fun s => G s ^ 2 - poleClearedFirstTraceExponentialContinuation s
  have hHana : AnalyticOnNhd ℂ H rightHalf :=
    ((hGdiff.analyticOnNhd isOpen_rightHalf).pow 2).sub
      analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hmem : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf :=
      isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 := hmem.mono fun s hs => by
      dsimp [H]
      rw [hGeq hs, poleClearedFirstTraceSourceLimit_sq hs, sub_self]
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have hHall := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_rightHalf.isPreconnected (farHalf_subset_rightHalf two_mem_farHalf) hfreq
  intro s hs
  have hzero := hHall hs
  change G s ^ 2 - poleClearedFirstTraceExponentialContinuation s = 0 at hzero
  exact sub_eq_zero.mp hzero

end

end RHTower
