import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteNoGo
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.HardyStieltjesDeterminacy

/-!
# Unbounded moving-Hermite depth forces a flat impossible limit

The boundary-Hermite counterterm subtracts the degree-`K` Taylor polynomial of the positively
dressed source at `b = 6/11`.  Consequently the corrected source, and hence the full pole-cleared
approximant, has an exact zero of order at least `K + 1` at `b`.

If `K = depth N` tends to infinity, every fixed jet is eventually zero.  Local boundedness and
Euler admissibility would give a locally uniform holomorphic Vitali limit on `rightHalf`; Cauchy
derivative convergence then makes that limit flat at `b`.  Analytic germ determinacy and the
identity theorem make it identically zero, contradicting its nonzero Euler value at `s = 2`.

This rate-free obstruction includes exact critical slope `5/11`.  It shows that the phase boundary
seen by earlier pointwise growth estimates is not a surviving point-Hermite regime.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Derivatives of a translated monomial at its center retain only the matching degree. -/
theorem iteratedDeriv_sub_pow_at_center (c : ℂ) (j k : ℕ) :
    iteratedDeriv j (fun s : ℂ => (s - c) ^ k) c =
      if j = k then (k.factorial : ℂ) else 0 := by
  have hshift := congrFun
    (_root_.iteratedDeriv_comp_sub_const j (fun z : ℂ => z ^ k) c) c
  rw [show c - c = (0 : ℂ) by ring] at hshift
  rw [hshift]
  simpa using
    (_root_.iteratedDeriv_fun_pow_zero :
      iteratedDeriv j (fun z : ℂ => z ^ k) 0 =
        ((if j = k then k.factorial else 0 : ℕ) : ℂ))

private theorem iteratedDeriv_finset_sum_of_analyticAt
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (x : ℂ) (k : ℕ)
    (h : ∀ i ∈ s, AnalyticAt ℂ (F i) x) :
    iteratedDeriv k (fun z => ∑ i ∈ s, F i z) x =
      ∑ i ∈ s, iteratedDeriv k (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      have hA : AnalyticAt ℂ (F a) x := h a (Finset.mem_insert_self a t)
      have hT : ∀ i ∈ t, AnalyticAt ℂ (F i) x := fun i hi =>
        h i (Finset.mem_insert_of_mem hi)
      have hTsum : AnalyticAt ℂ (fun z => ∑ i ∈ t, F i z) x := by
        have hsum := Finset.analyticAt_sum t hT
        have heq : (∑ i ∈ t, F i) = fun z => ∑ i ∈ t, F i z := by
          funext z
          simp
        rwa [heq] at hsum
      have hsplit : (fun z => ∑ i ∈ insert a t, F i z) =
          fun z => F a z + ∑ i ∈ t, F i z := by
        funext z
        rw [Finset.sum_insert ha]
      have hpi : (fun z => F a z + ∑ i ∈ t, F i z) =
          F a + fun z => ∑ i ∈ t, F i z := rfl
      rw [hsplit, hpi, iteratedDeriv_add hA.contDiffAt hTsum.contDiffAt,
        ih hT, Finset.sum_insert ha]

/-- The degree-`K` Hermite polynomial reproduces every dressed-source jet through order `K`. -/
theorem iteratedDeriv_boundaryHermiteJetPolynomial_at_boundary
    (N K j : ℕ) (hj : j ≤ K) :
    iteratedDeriv j (boundaryHermiteJetPolynomial N K) boundaryExteriorPoint =
      iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint := by
  classical
  unfold boundaryHermiteJetPolynomial
  change iteratedDeriv j
    (fun z : ℂ => ∑ k ∈ Finset.range (K + 1),
      iteratedDeriv k (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
          (k.factorial : ℂ) * (z - boundaryExteriorPoint) ^ k)
      boundaryExteriorPoint = _
  rw [iteratedDeriv_finset_sum_of_analyticAt]
  · rw [Finset.sum_eq_single j]
    · have hmul := _root_.iteratedDeriv_const_mul_field
        (n := j) (x := boundaryExteriorPoint)
        (iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
          (j.factorial : ℂ))
        (fun z : ℂ => (z - boundaryExteriorPoint) ^ j)
      rw [hmul, iteratedDeriv_sub_pow_at_center, if_pos rfl]
      have hfac : (j.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      field_simp
    · intro k _ hkj
      have hmul := _root_.iteratedDeriv_const_mul_field
        (n := j) (x := boundaryExteriorPoint)
        (iteratedDeriv k (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
          (k.factorial : ℂ))
        (fun z : ℂ => (z - boundaryExteriorPoint) ^ k)
      rw [hmul, iteratedDeriv_sub_pow_at_center, if_neg (Ne.symm hkj)]
      simp
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)))
  · intro k _
    fun_prop

/-- The positive and negative exponential dresses cancel exactly. -/
theorem boundaryExponentialSeparator_mul_boundaryPositiveExponentialSeparator
    (N : ℕ) (s : ℂ) :
    boundaryExponentialSeparator N s * boundaryPositiveExponentialSeparator N s = 1 := by
  rw [boundaryExponentialSeparator, boundaryPositiveExponentialSeparator,
    ← Complex.exp_add]
  convert Complex.exp_zero using 1
  ring_nf

/-- Corrected source equals the negative dress times the exact Taylor remainder. -/
theorem boundaryHermiteJet_correctedSource_eq_separator_mul_remainder
    (N K : ℕ) (s : ℂ) :
    squarefreeHalfDirichletPartialSum N s + boundaryHermiteJetCounterterm N K s =
      boundaryExponentialSeparator N s *
        (boundaryPositiveExponentialDress N s - boundaryHermiteJetPolynomial N K s) := by
  rw [boundaryHermiteJetCounterterm, boundaryPositiveExponentialDress]
  have hsep := boundaryExponentialSeparator_mul_boundaryPositiveExponentialSeparator N s
  calc
    squarefreeHalfDirichletPartialSum N s +
        -boundaryExponentialSeparator N s * boundaryHermiteJetPolynomial N K s =
      (boundaryExponentialSeparator N s * boundaryPositiveExponentialSeparator N s) *
          squarefreeHalfDirichletPartialSum N s -
        boundaryExponentialSeparator N s * boundaryHermiteJetPolynomial N K s := by
          rw [hsep]
          ring
    _ = _ := by ring

private theorem iteratedDeriv_mul_eq_zero_of_right_jets
    {f g : ℂ → ℂ} {z : ℂ} {j : ℕ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hzero : ∀ q ≤ j, iteratedDeriv q g z = 0) :
    iteratedDeriv j (fun s => f s * g s) z = 0 := by
  change iteratedDeriv j (f * g) z = 0
  rw [_root_.iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero (j - i) (Nat.sub_le j i)]
  simp

/-- The Hermite-corrected arithmetic source has zero jets through its interpolation depth. -/
theorem iteratedDeriv_boundaryHermiteJet_correctedSource_at_boundary
    (N K j : ℕ) (hj : j ≤ K) :
    iteratedDeriv j
      (fun s => squarefreeHalfDirichletPartialSum N s +
        boundaryHermiteJetCounterterm N K s)
      boundaryExteriorPoint = 0 := by
  have hfun :
      (fun s => squarefreeHalfDirichletPartialSum N s +
        boundaryHermiteJetCounterterm N K s) =
      fun s => boundaryExponentialSeparator N s *
        (boundaryPositiveExponentialDress N s - boundaryHermiteJetPolynomial N K s) := by
    funext s
    exact boundaryHermiteJet_correctedSource_eq_separator_mul_remainder N K s
  rw [hfun]
  apply iteratedDeriv_mul_eq_zero_of_right_jets
    ((analytic_boundaryExponentialSeparator N) boundaryExteriorPoint (Set.mem_univ _))
    (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)).sub
        (analytic_boundaryHermiteJetPolynomial N K) boundaryExteriorPoint (Set.mem_univ _))
  intro q hq
  rw [_root_.iteratedDeriv_sub
    (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N))
        boundaryExteriorPoint (Set.mem_univ _)).contDiffAt
    ((analytic_boundaryHermiteJetPolynomial N K)
      boundaryExteriorPoint (Set.mem_univ _)).contDiffAt,
    iteratedDeriv_boundaryHermiteJetPolynomial_at_boundary N K q (hq.trans hj)]
  change iteratedDeriv q (boundaryPositiveExponentialDress N) boundaryExteriorPoint -
      iteratedDeriv q (boundaryPositiveExponentialDress N) boundaryExteriorPoint = 0
  exact sub_self _

/-- Analytic pole and determinant factors preserve the scheduled corrected source's zero jet. -/
theorem iteratedDeriv_poleClearedFirstTrace_boundaryHermiteJetCountertermScheduledApprox_at_boundary
    (depth kappa : ℕ → ℕ) (N j : ℕ) (hj : j ≤ depth N) :
    iteratedDeriv j
      (poleClearedFirstTraceCountertermScheduledApprox
        (fun M => boundaryHermiteJetCounterterm M (depth M)) kappa N)
      boundaryExteriorPoint = 0 := by
  let corrected : ℂ → ℂ := fun s =>
    squarefreeHalfDirichletPartialSum N s +
      boundaryHermiteJetCounterterm N (depth N) s
  let prefactor : ℂ → ℂ := fun s =>
    poleFactorSqrtApprox (kappa N) s / squarefreeCarlemanHalfDet s
  have hfun :
      poleClearedFirstTraceCountertermScheduledApprox
          (fun M => boundaryHermiteJetCounterterm M (depth M)) kappa N =
        fun s => prefactor s * corrected s := by
    funext s
    simp only [poleClearedFirstTraceCountertermScheduledApprox, prefactor, corrected]
    ring
  rw [hfun]
  apply iteratedDeriv_mul_eq_zero_of_right_jets
  · exact ((analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N)).div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s))
        boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  · exact (((analyticOnNhd_squarefreeHalfDirichletPartialSum N).mono
      (Set.subset_univ rightHalf)).add
        (analyticOnNhd_boundaryHermiteJetCounterterm N (depth N)))
          boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  · intro q hq
    exact iteratedDeriv_boundaryHermiteJet_correctedSource_at_boundary
      N (depth N) q (hq.trans hj)

/-- **Unbounded-depth point-Hermite no-go.** If Hermite depth and pole-factor schedule are
cofinal, Euler admissibility and local boundedness cannot hold simultaneously. -/
theorem not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm_of_depth_tendsto_atTop
    {depth kappa : ℕ → ℕ}
    (hdepth : Tendsto depth atTop atTop)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ (SquarefreeHalfCountertermAdmissible
          (fun N => boundaryHermiteJetCounterterm N (depth N)) ∧
        PoleClearedFirstTraceCountertermScheduledLocallyBounded
          (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa) := by
  rintro ⟨hadm, hloc⟩
  let counterterm : ℕ → ℂ → ℂ :=
    fun N => boundaryHermiteJetCounterterm N (depth N)
  let F : ℕ → ℂ → ℂ :=
    poleClearedFirstTraceCountertermScheduledApprox counterterm kappa
  have hadm' : SquarefreeHalfCountertermAdmissible counterterm := by
    simpa [counterterm] using hadm
  have hloc' : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
    simpa [counterterm] using hloc
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N =>
        (analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
          hadm' kappa N).differentiableOn)
      hloc'
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        (tendstoLocallyUniformlyOn_poleClearedFirstTraceCountertermScheduledApprox
          hadm' hkappa).tendsto_at hs⟩)
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      ((tendstoLocallyUniformlyOn_poleClearedFirstTraceCountertermScheduledApprox
        hadm' hkappa).tendsto_at hs)
  have hFdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ (F N) rightHalf :=
    Filter.Eventually.of_forall fun N =>
      (analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
        hadm' kappa N).differentiableOn
  have hGjet : ∀ j : ℕ, iteratedDeriv j G boundaryExteriorPoint = 0 := by
    intro j
    have hjetLimit := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
      isOpen_rightHalf hGlim hFdiff j boundaryExteriorPoint_mem_rightHalf
    have hdepthj : ∀ᶠ N in atTop, j ≤ depth N :=
      hdepth.eventually (eventually_ge_atTop j)
    have hzeroLimit : Tendsto
        (fun N => iteratedDeriv j (F N) boundaryExteriorPoint)
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hdepthj] with N hN
      symm
      exact
        iteratedDeriv_poleClearedFirstTrace_boundaryHermiteJetCountertermScheduledApprox_at_boundary
          depth kappa N j hN
    exact tendsto_nhds_unique hjetLimit hzeroLimit
  have hGana : AnalyticOnNhd ℂ G rightHalf :=
    hGdiff.analyticOnNhd isOpen_rightHalf
  have hlocal : G =ᶠ[𝓝 boundaryExteriorPoint] (fun _ : ℂ => (0 : ℂ)) := by
    apply HTGeometry.analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
    · exact hGana boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
    · exact analyticAt_const
    · intro j
      simpa using hGjet j
  have hzeroAna : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) rightHalf := by
    exact analyticOnNhd_const
  have hGall : EqOn G (fun _ : ℂ => (0 : ℂ)) rightHalf :=
    hGana.eqOn_of_preconnected_of_eventuallyEq hzeroAna
      convex_rightHalf.isPreconnected boundaryExteriorPoint_mem_rightHalf hlocal
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

/-- An unbounded natural-valued sequence admits a cofinal index map along which its values tend to
infinity. The finite-prefix sum forces cofinality even though the chosen map need not be monotone. -/
theorem exists_cofinal_high_depth_subsequence
    {depth : ℕ → ℕ} (hunbounded : ∀ j : ℕ, ∃ N : ℕ, j ≤ depth N) :
    ∃ phi : ℕ → ℕ,
      Tendsto phi atTop atTop ∧
      Tendsto (depth ∘ phi) atTop atTop ∧
      ∀ j : ℕ, j ≤ depth (phi j) := by
  choose phi hphiDepth using hunbounded
  refine ⟨phi, ?_, ?_, hphiDepth⟩
  · apply Filter.tendsto_atTop.2
    intro B
    let M : ℕ := ∑ m ∈ Finset.range B, (depth m + 1)
    filter_upwards [eventually_ge_atTop M] with n hn
    by_contra hnot
    have hlt : phi n < B := Nat.lt_of_not_ge hnot
    have hsingle : depth (phi n) + 1 ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (depth i + 1))
        (Finset.mem_range.mpr hlt)
    have hnDepth : n ≤ depth (phi n) := hphiDepth n
    omega
  · apply Filter.tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop B] with n hn
    exact hn.trans (hphiDepth n)

private theorem tendstoLocallyUniformlyOn_comp_cofinal_index
    {ι κ α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f p s) {k : κ → ι} (hk : Tendsto k q p) :
    TendstoLocallyUniformlyOn (fun n => F (k n)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := hF u hu x hx
  exact ⟨t, ht, hk.eventually hev⟩

/-- An unbounded, possibly oscillatory, depth range contains a cofinal flatness subsequence, so it
is subject to the same impossible-limit obstruction as a depth schedule tending to infinity. -/
theorem not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm_of_depth_range_unbounded
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ j : ℕ, ∃ N : ℕ, j ≤ depth N)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ (SquarefreeHalfCountertermAdmissible
          (fun N => boundaryHermiteJetCounterterm N (depth N)) ∧
        PoleClearedFirstTraceCountertermScheduledLocallyBounded
          (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa) := by
  rintro ⟨hadm, hloc⟩
  obtain ⟨phi, hphi, hdepthPhi, _⟩ := exists_cofinal_high_depth_subsequence hdepth
  let counterterm : ℕ → ℂ → ℂ :=
    fun N => boundaryHermiteJetCounterterm N (depth N)
  let F : ℕ → ℂ → ℂ := fun n =>
    poleClearedFirstTraceCountertermScheduledApprox counterterm kappa (phi n)
  have hadm' : SquarefreeHalfCountertermAdmissible counterterm := by
    simpa [counterterm] using hadm
  have hloc' : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
    simpa [counterterm] using hloc
  have hEuler :
      TendstoLocallyUniformlyOn F poleClearedFirstTraceSourceLimit atTop farHalf := by
    exact tendstoLocallyUniformlyOn_comp_cofinal_index
      (tendstoLocallyUniformlyOn_poleClearedFirstTraceCountertermScheduledApprox
        hadm' hkappa) hphi
  have hlocSub :
      ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
        ∀ n, ∀ w ∈ ball z R, ‖F n w‖ ≤ C := by
    intro z hz
    obtain ⟨R, hR, hball, C, hC⟩ := hloc' z hz
    exact ⟨R, hR, hball, C, fun n w hw => hC (phi n) w hw⟩
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun n =>
        (analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
          hadm' kappa (phi n)).differentiableOn)
      hlocSub
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
  have hFdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) rightHalf :=
    Filter.Eventually.of_forall fun n =>
      (analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
        hadm' kappa (phi n)).differentiableOn
  have hGjet : ∀ j : ℕ, iteratedDeriv j G boundaryExteriorPoint = 0 := by
    intro j
    have hjetLimit := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
      isOpen_rightHalf hGlim hFdiff j boundaryExteriorPoint_mem_rightHalf
    have hdepthj : ∀ᶠ n in atTop, j ≤ depth (phi n) :=
      hdepthPhi.eventually (eventually_ge_atTop j)
    have hzeroLimit : Tendsto
        (fun n => iteratedDeriv j (F n) boundaryExteriorPoint)
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hdepthj] with n hn
      symm
      exact
        iteratedDeriv_poleClearedFirstTrace_boundaryHermiteJetCountertermScheduledApprox_at_boundary
          depth kappa (phi n) j hn
    exact tendsto_nhds_unique hjetLimit hzeroLimit
  have hGana : AnalyticOnNhd ℂ G rightHalf :=
    hGdiff.analyticOnNhd isOpen_rightHalf
  have hlocal : G =ᶠ[𝓝 boundaryExteriorPoint] (fun _ : ℂ => (0 : ℂ)) := by
    apply HTGeometry.analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
    · exact hGana boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
    · exact analyticAt_const
    · intro j
      simpa using hGjet j
  have hzeroAna : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) rightHalf := by
    exact analyticOnNhd_const
  have hGall : EqOn G (fun _ : ℂ => (0 : ℂ)) rightHalf :=
    hGana.eqOn_of_preconnected_of_eventuallyEq hzeroAna
      convex_rightHalf.isPreconnected boundaryExteriorPoint_mem_rightHalf hlocal
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

/-- **Complete fixed-anchor point-Hermite no-go.** No depth schedule—bounded, increasing, or
oscillatory—can make the canonical counterterm both Euler-admissible and locally bounded along a
cofinal pole-factor schedule. -/
theorem not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm
    {depth kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    ¬ (SquarefreeHalfCountertermAdmissible
          (fun N => boundaryHermiteJetCounterterm N (depth N)) ∧
        PoleClearedFirstTraceCountertermScheduledLocallyBounded
          (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa) := by
  by_cases hbounded : ∃ B : ℕ, ∀ N : ℕ, depth N ≤ B
  · obtain ⟨B, hB⟩ := hbounded
    rintro ⟨_, hloc⟩
    apply
      (no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_one_div_54
        (kappa := kappa) (depth := depth) ?_ hkappa) hloc
    filter_upwards [eventually_ge_atTop (54 * B)] with N hN
    have hdR : (depth N : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hB N
    have hNR : (54 : ℝ) * (B : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    nlinarith
  · have hunbounded : ∀ j : ℕ, ∃ N : ℕ, j ≤ depth N := by
      intro j
      by_contra hnot
      apply hbounded
      refine ⟨j, fun N => ?_⟩
      exact (Nat.lt_of_not_ge (not_exists.mp hnot N)).le
    exact
      not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm_of_depth_range_unbounded
        hunbounded hkappa

end

end RHTower
