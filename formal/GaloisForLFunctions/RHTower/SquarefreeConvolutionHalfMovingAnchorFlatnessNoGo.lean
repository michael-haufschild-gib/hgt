import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo

/-!
# Moving-anchor flatness obstruction

Moving an interpolation anchor does not evade the point-Hermite obstruction when the anchors have
an interior limit.  A locally bounded Euler-faithful holomorphic family has a Vitali limit on
`rightHalf`.  Local uniform convergence passes to every derivative, and local uniform convergence
at moving arguments transports increasing zero jets at anchors converging inside the domain to a
complete zero jet of the limit.  Analytic rigidity then contradicts the nonzero Euler germ.

Thus any viable high-depth moving-anchor construction must escape every compact subset of
`rightHalf`; motion inside a compact region is not enough.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Moving-anchor interior-cluster no-go.** An Euler-faithful locally bounded holomorphic family
cannot have zeros of increasing order at anchors converging within `rightHalf`. -/
theorem not_eulerFaithful_locallyBounded_of_moving_flat_anchors
    {F : ℕ → ℂ → ℂ} {anchor : ℕ → ℂ} {depth : ℕ → ℕ} {b : ℂ}
    (hFana : ∀ N, AnalyticOnNhd ℂ (F N) rightHalf)
    (hloc : ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
      ∀ N, ∀ w ∈ ball z R, ‖F N w‖ ≤ C)
    (hEuler : TendstoLocallyUniformlyOn F poleClearedFirstTraceSourceLimit atTop farHalf)
    (hb : b ∈ rightHalf)
    (hanchor : Tendsto anchor atTop (𝓝[rightHalf] b))
    (hdepth : Tendsto depth atTop atTop)
    (hjet : ∀ N j, j ≤ depth N → iteratedDeriv j (F N) (anchor N) = 0) :
    False := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N => (hFana N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s, hEuler.tendsto_at hs⟩)
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      (hEuler.tendsto_at hs)
  have hFdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ (F N) rightHalf :=
    Filter.Eventually.of_forall fun N => (hFana N).differentiableOn
  have hGjet : ∀ j : ℕ, iteratedDeriv j G b = 0 := by
    intro j
    have hderLU :=
      GaloisForLFunctions.iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
        isOpen_rightHalf hGlim hFdiff j
    have hGderCont : ContinuousWithinAt (iteratedDeriv j G) rightHalf b :=
      (GaloisForLFunctions.differentiableOn_iteratedDeriv
        isOpen_rightHalf hGdiff j).continuousOn b hb
    have hmoving : Tendsto
        (fun N => iteratedDeriv j (F N) (anchor N)) atTop
        (𝓝 (iteratedDeriv j G b)) :=
      hderLU.tendsto_comp hGderCont hb hanchor
    have hdepthj : ∀ᶠ N in atTop, j ≤ depth N :=
      hdepth.eventually (eventually_ge_atTop j)
    have hzeroLimit : Tendsto
        (fun N => iteratedDeriv j (F N) (anchor N)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hdepthj] with N hN
      exact (hjet N j hN).symm
    exact tendsto_nhds_unique hmoving hzeroLimit
  have hGana : AnalyticOnNhd ℂ G rightHalf :=
    hGdiff.analyticOnNhd isOpen_rightHalf
  have hlocal : G =ᶠ[𝓝 b] (fun _ : ℂ => (0 : ℂ)) := by
    apply HTGeometry.analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
    · exact hGana b hb
    · exact analyticAt_const
    · intro j
      simpa using hGjet j
  have hzeroAna : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) rightHalf := by
    exact analyticOnNhd_const
  have hGall : EqOn G (fun _ : ℂ => (0 : ℂ)) rightHalf :=
    hGana.eqOn_of_preconnected_of_eventuallyEq hzeroAna
      convex_rightHalf.isPreconnected hb hlocal
  have hsourceSq := poleClearedFirstTraceSourceLimit_sq two_mem_farHalf
  have hcontinuationNe : poleClearedFirstTraceExponentialContinuation (2 : ℂ) ≠ 0 := by
    rw [poleClearedFirstTraceExponentialContinuation_eq_sub_one_mul_exp_primeZeta
      (mem_farHalf.mp two_mem_farHalf)]
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have hsourceNe : poleClearedFirstTraceSourceLimit (2 : ℂ) ≠ 0 := by
    intro hzero
    have hzeroContinuation : (0 : ℂ) =
        poleClearedFirstTraceExponentialContinuation (2 : ℂ) := by
      simpa [hzero] using hsourceSq
    exact hcontinuationNe hzeroContinuation.symm
  apply hsourceNe
  rw [← hGeq two_mem_farHalf]
  exact hGall (farHalf_subset_rightHalf two_mem_farHalf)

private theorem tendstoLocallyUniformlyOn_comp_index
    {ι κ α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f p s) {k : κ → ι} (hk : Tendsto k q p) :
    TendstoLocallyUniformlyOn (fun n => F (k n)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := hF u hu x hx
  exact ⟨t, ht, hk.eventually hev⟩

/-- **Compact-escape classification.** Under the moving-zero-jet hypotheses, anchors eventually
avoid every compact subset of `rightHalf`. -/
theorem moving_flat_anchors_eventually_avoid_compact
    {F : ℕ → ℂ → ℂ} {anchor : ℕ → ℂ} {depth : ℕ → ℕ}
    (hFana : ∀ N, AnalyticOnNhd ℂ (F N) rightHalf)
    (hloc : ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
      ∀ N, ∀ w ∈ ball z R, ‖F N w‖ ≤ C)
    (hEuler : TendstoLocallyUniformlyOn F poleClearedFirstTraceSourceLimit atTop farHalf)
    (hdepth : Tendsto depth atTop atTop)
    (hjet : ∀ N j, j ≤ depth N → iteratedDeriv j (F N) (anchor N) = 0)
    {K : Set ℂ} (hKcompact : IsCompact K) (hKright : K ⊆ rightHalf) :
    ∀ᶠ N in atTop, anchor N ∉ K := by
  by_contra hnot
  have hfreq : ∃ᶠ N in atTop, anchor N ∈ K := by
    rw [Filter.not_eventually] at hnot
    simpa only [not_not] using hnot
  obtain ⟨b, hbK, phi, hphiMono, hanchor⟩ := hKcompact.tendsto_subseq' hfreq
  have hb : b ∈ rightHalf := hKright hbK
  have hphi : Tendsto phi atTop atTop := hphiMono.tendsto_atTop
  have hanchorWithin : Tendsto (anchor ∘ phi) atTop (𝓝[rightHalf] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hanchor, ?_⟩
    exact hanchor.eventually (isOpen_rightHalf.mem_nhds hb)
  apply not_eulerFaithful_locallyBounded_of_moving_flat_anchors
    (F := fun n => F (phi n)) (anchor := anchor ∘ phi) (depth := depth ∘ phi)
    (b := b)
  · exact fun n => hFana (phi n)
  · intro z hz
    obtain ⟨R, hR, hball, C, hC⟩ := hloc z hz
    exact ⟨R, hR, hball, C, fun n w hw => hC (phi n) w hw⟩
  · exact tendstoLocallyUniformlyOn_comp_index hEuler hphi
  · exact hb
  · exact hanchorWithin
  · exact hdepth.comp hphi
  · intro n j hj
    exact hjet (phi n) j hj

end

end RHTower
