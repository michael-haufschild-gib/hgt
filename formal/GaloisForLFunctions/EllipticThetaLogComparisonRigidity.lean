import GaloisForLFunctions.EllipticThetaLogComparison
import GaloisForLFunctions.CompactEllipticPoleFiniteness
import Mathlib.Analysis.Complex.Liouville

/-!
# Rigidity of the constructed-versus-analytic theta comparison

The globally meromorphic comparison has no poles after canonical normalisation. Its two local
period constraints extend across the removable divisor, making the normalised comparison entire
and doubly periodic. Compact fundamental-domain reduction and Liouville then force constancy.
-/

open Complex Set Filter Topology Function Metric

namespace GaloisForLFunctions

noncomputable section

/-- Canonical normal-form representative of the constructed-versus-analytic discrepancy. -/
def ellipticThetaLogComparisonNF (τ : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (ellipticThetaLogComparison τ) Set.univ

/-- Cancellation of every possible pole makes the canonical comparison entire. -/
theorem analyticOnNhd_ellipticThetaLogComparisonNF {τ : ℂ} (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (ellipticThetaLogComparisonNF τ) Set.univ := by
  have hM := meromorphicOn_ellipticThetaLogComparison hτ
  have hNF : MeromorphicNFOn (ellipticThetaLogComparisonNF τ) Set.univ := by
    exact meromorphicNFOn_toMeromorphicNFOn
      (ellipticThetaLogComparison τ) Set.univ
  intro z _
  apply (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [ellipticThetaLogComparisonNF,
    meromorphicOrderAt_toMeromorphicNFOn hM (Set.mem_univ z)]
  exact meromorphicOrderAt_ellipticThetaLogComparison_nonneg hτ

/-- The raw comparison is locally `τ`-periodic on every punctured neighborhood, including at its
removable divisor. -/
theorem ellipticThetaLogComparison_eventually_add_tau
    {τ z : ℂ} (hτ : 0 < τ.im) :
    ∀ᶠ w in 𝓝[≠] z,
      ellipticThetaLogComparison τ (w + τ) = ellipticThetaLogComparison τ w := by
  by_cases hz : jacobiTheta₂ z τ = 0
  · rw [jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ] at hz
    obtain ⟨m, n, rfl⟩ := hz
    exact ellipticThetaLogComparison_eventually_add_tau_eq_lattice hτ m n
  · have hcoord : ellipticThetaCoordinate τ z ≠ 1 := by
      intro hcoord
      apply hz
      exact (ellipticThetaCoordinate_mem_nomeOrbit_iff_jacobiTheta₂_zero hτ).mp
        ⟨0, by simpa using hcoord⟩
    have hthetaEv : ∀ᶠ w in 𝓝 z, jacobiTheta₂ w τ ≠ 0 := by
      exact ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)).continuousAt.eventually_ne hz
    have hcoordEv : ∀ᶠ w in 𝓝 z, ellipticThetaCoordinate τ w ≠ 1 := by
      exact (analyticAt_ellipticThetaCoordinate τ z).continuousAt.eventually_ne hcoord
    filter_upwards [hthetaEv.filter_mono inf_le_left,
      hcoordEv.filter_mono inf_le_left] with w hwtheta hwcoord
    exact ellipticThetaLogComparison_add_tau hτ hwcoord hwtheta

/-- A locally punctured-periodic meromorphic function transfers that period to its entire
canonical normal form. -/
theorem periodic_toMeromorphicNFOn_of_eventually_punctured
    {f F : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    (hFdef : F = toMeromorphicNFOn f Set.univ)
    (hFan : AnalyticOnNhd ℂ F Set.univ) (p : ℂ)
    (hlocal : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + p) = f w) :
    Function.Periodic F p := by
  intro z
  have hFz : F =ᶠ[𝓝[≠] z] f := by
    rw [hFdef]
    exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hFzp : F =ᶠ[𝓝[≠] (z + p)] f := by
    rw [hFdef]
    exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ (z + p))
  have ht : Tendsto (fun w : ℂ => w + p) (𝓝[≠] z) (𝓝[≠] (z + p)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (continuousAt_id.add continuousAt_const).tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa using hw
  have hshift : (fun w => F (w + p)) =ᶠ[𝓝[≠] z] (fun w => f (w + p)) :=
    ht.eventually hFzp
  have heq : (fun w => F (w + p)) =ᶠ[𝓝[≠] z] F := by
    filter_upwards [hshift, hlocal z, hFz] with w h₁ h₂ h₃
    rw [h₁, h₂, ← h₃]
  have hcontF : ContinuousAt F z := (hFan z (Set.mem_univ z)).continuousAt
  have hcontShift : ContinuousAt (fun w => F (w + p)) z := by
    have hs : ContinuousAt (fun w : ℂ => w + p) z :=
      continuousAt_id.add continuousAt_const
    simpa only [Function.comp_def] using
      (hFan (z + p) (Set.mem_univ (z + p))).continuousAt.comp_of_eq hs rfl
  exact Filter.EventuallyEq.eq_of_nhds
    ((hcontShift.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcontF).mp heq)

/-- The canonical comparison has period one. -/
theorem ellipticThetaLogComparisonNF_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    Function.Periodic (ellipticThetaLogComparisonNF τ) 1 := by
  apply periodic_toMeromorphicNFOn_of_eventually_punctured
    (meromorphicOn_ellipticThetaLogComparison hτ) rfl
    (analyticOnNhd_ellipticThetaLogComparisonNF hτ)
  intro z
  filter_upwards with w
  exact ellipticThetaLogComparison_add_one τ w

/-- The canonical comparison has period `τ`. -/
theorem ellipticThetaLogComparisonNF_add_tau {τ : ℂ} (hτ : 0 < τ.im) :
    Function.Periodic (ellipticThetaLogComparisonNF τ) τ := by
  apply periodic_toMeromorphicNFOn_of_eventually_punctured
    (meromorphicOn_ellipticThetaLogComparison hτ) rfl
    (analyticOnNhd_ellipticThetaLogComparisonNF hτ)
  exact fun z => ellipticThetaLogComparison_eventually_add_tau hτ

/-- The canonical comparison is constant: it is entire, doubly periodic, and bounded after
reduction to a compact fundamental parallelogram. -/
theorem ellipticThetaLogComparisonNF_constant {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ z w, ellipticThetaLogComparisonNF τ z = ellipticThetaLogComparisonNF τ w := by
  let F := ellipticThetaLogComparisonNF τ
  have hA := analyticOnNhd_ellipticThetaLogComparisonNF hτ
  have hdiff : Differentiable ℂ F := fun z => (hA z (Set.mem_univ z)).differentiableAt
  have hcont : Continuous F := hdiff.continuous
  have hpOne : Function.Periodic F 1 := ellipticThetaLogComparisonNF_add_one hτ
  have hpTau : Function.Periodic F τ := ellipticThetaLogComparisonNF_add_tau hτ
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) (1 + ‖τ‖)).bddAbove_image hcont.norm.continuousOn
  have hglobal : ∀ z, ‖F z‖ ≤ C := by
    intro z
    let r := ellipticReduce τ z
    have hr : r ∈ closedBall (0 : ℂ) (1 + ‖τ‖) := by
      simpa [mem_closedBall] using ellipticReduce_norm_le τ z
    have hFr : ‖F r‖ ≤ C := hC (mem_image_of_mem (fun w => ‖F w‖) hr)
    have hdecomp := ellipticReduce_lattice_decomposition
      (τ := τ) (z := z) (ne_of_gt hτ)
    have hOneM := hpOne.int_mul ⌊tauCoordX τ z⌋
    have hTauN := hpTau.int_mul ⌊tauCoordY τ z⌋
    have hFzr : F z = F r := by
      rw [hdecomp]
      rw [hTauN (r + (⌊tauCoordX τ z⌋ : ℂ))]
      simpa using hOneM r
    rw [hFzr]
    exact hFr
  have hbounded : Bornology.IsBounded (Set.range F) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro y ⟨z, rfl⟩; exact hglobal z⟩
  exact fun z w => hdiff.apply_eq_apply_of_bounded hbounded z w

/-- On the common regular locus, the raw comparison equals one parameter-dependent constant. -/
theorem ellipticThetaLogComparison_eq_constant_off_divisor {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ c : ℂ, ∀ z, jacobiTheta₂ z τ ≠ 0 → ellipticThetaLogComparison τ z = c := by
  let F := ellipticThetaLogComparisonNF τ
  refine ⟨F 0, ?_⟩
  intro z hz
  have hM := meromorphicOn_ellipticThetaLogComparison hτ
  have hNFAt : MeromorphicNFAt (ellipticThetaLogComparison τ) z :=
    (analyticAt_ellipticThetaLogComparison_of_jacobiTheta₂_ne hτ hz).meromorphicNFAt
  have hFz : F z = ellipticThetaLogComparison τ z := by
    dsimp [F, ellipticThetaLogComparisonNF]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (Set.mem_univ z)]
    have heq := toMeromorphicNFAt_eq_self.mpr hNFAt
    rw [heq]
  rw [← hFz]
  exact ellipticThetaLogComparisonNF_constant hτ z 0

/-- Constraint-and-divisor uniqueness: the constructed theta boundary is the analytic Jacobi
logarithmic derivative up to a constant independent of the additive variable. -/
theorem ellipticThetaAdditiveLogKernel_eq_thetaLogDeriv_add_constant
    {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ c : ℂ, ∀ z, jacobiTheta₂ z τ ≠ 0 →
      ellipticThetaAdditiveLogKernel τ z = thetaLogDeriv z τ + c := by
  obtain ⟨c, hc⟩ := ellipticThetaLogComparison_eq_constant_off_divisor hτ
  refine ⟨c, ?_⟩
  intro z hz
  have h := hc z hz
  rw [ellipticThetaLogComparison] at h
  linear_combination h

/-- Every translated defect of the constructed product kernel is exactly the corresponding
analytic Jacobi-theta logarithmic-derivative defect. The constant comparison ambiguity cancels. -/
theorem ellipticThetaAdditiveLogKernel_defect_eq_thetaLogDerivDefect
    {τ h z : ℂ} (hτ : 0 < τ.im)
    (hz : jacobiTheta₂ z τ ≠ 0) (hzh : jacobiTheta₂ (z + h) τ ≠ 0) :
    ellipticThetaAdditiveLogKernel τ (z + h) -
        ellipticThetaAdditiveLogKernel τ z =
      thetaLogDeriv (z + h) τ - thetaLogDeriv z τ := by
  obtain ⟨c, hc⟩ := ellipticThetaAdditiveLogKernel_eq_thetaLogDeriv_add_constant hτ
  rw [hc z hz, hc (z + h) hzh]
  ring

end

end GaloisForLFunctions
