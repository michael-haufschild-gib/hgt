import GaloisForLFunctions.RHTower.PoleFactorCayleySqrtApproximation
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfEulerSummability
import GaloisForLFunctions.HTGeometry.VitaliConvergence

/-!
# A source-defined Vitali criterion for the first multiplicity rung

Let `a` be the canonical Dirichlet-convolution square root of the squarefree indicator.  Multiply
its Dirichlet-polynomial truncations by the rational Cayley approximants to `sqrt (s - 1)` and
divide by the explicit square root of the Carleman determinant.  Every resulting function is
holomorphic on `Re s > 1/2`.  On `Re s > 1` the sequence converges compact-open to a function whose
square is the pole-cleared first-trace continuation.

Vitali therefore reduces the remaining continuation problem to local boundedness of this one
explicit arithmetic sequence.  This is a bridge, not a proof of that bound: the Cayley factors
are not themselves normal across `s = 1`, so the hypothesis demands genuine synchronized
cancellation from the coefficient truncations.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical Dirichlet-polynomial truncations of the convolution half. -/
def squarefreeHalfDirichletPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, LSeries.term squarefreeConvolutionHalf s n

private theorem LSeries_term_differentiable (a : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (fun s : ℂ => LSeries.term a s n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [LSeries.term_zero] using (differentiable_const (c := (0 : ℂ)))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hfun : (fun s : ℂ => LSeries.term a s n) =
        fun s : ℂ => a n * (n : ℂ) ^ (-s) := by
      funext s
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
    rw [hfun]
    intro s
    exact (differentiableAt_const _).mul
      (DifferentiableAt.cpow (differentiableAt_const _) differentiableAt_id.neg
        (Complex.ofReal_mem_slitPlane.mpr hnpos))

theorem analyticOnNhd_squarefreeHalfDirichletPartialSum (N : ℕ) :
    AnalyticOnNhd ℂ (squarefreeHalfDirichletPartialSum N) Set.univ := by
  have hdiff : Differentiable ℂ (squarefreeHalfDirichletPartialSum N) := by
    intro s
    unfold squarefreeHalfDirichletPartialSum
    have hsum : DifferentiableAt ℂ
        (∑ n ∈ Finset.range N,
          fun z : ℂ => LSeries.term squarefreeConvolutionHalf z n) s := by
      apply DifferentiableAt.sum
      intro n hn
      exact LSeries_term_differentiable squarefreeConvolutionHalf n s
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with z
    simp only [Finset.sum_apply]
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

/-- Source-defined full-half-plane approximants to the pole-cleared first-trace half. -/
def poleClearedFirstTraceSourceApprox (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox N s * squarefreeHalfDirichletPartialSum N s /
    squarefreeCarlemanHalfDet s

/-- Euler-chamber compact-open limit of the source approximants. -/
def poleClearedFirstTraceSourceLimit (s : ℂ) : ℂ :=
  poleFactorSqrtCayleyLimit s * LSeries squarefreeConvolutionHalf s /
    squarefreeCarlemanHalfDet s

theorem analyticOnNhd_poleClearedFirstTraceSourceApprox_rightHalf (N : ℕ) :
    AnalyticOnNhd ℂ (poleClearedFirstTraceSourceApprox N) rightHalf := by
  exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf N).mul
    ((analyticOnNhd_squarefreeHalfDirichletPartialSum N).mono (Set.subset_univ _)) |>.div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)

theorem poleClearedFirstTraceSourceLimit_sq {s : ℂ} (hs : s ∈ farHalf) :
    poleClearedFirstTraceSourceLimit s ^ 2 =
      poleClearedFirstTraceExponentialContinuation s := by
  have hs' : 1 < s.re := mem_farHalf.mp hs
  rw [poleClearedFirstTraceSourceLimit, div_pow, mul_pow,
    poleFactorSqrtCayleyLimit_sq hs', LSeries_squarefreeConvolutionHalf_sq hs',
    squarefreeCarlemanHalfDet_sq,
    poleClearedFirstTraceExponentialContinuation_eq_sub_one_mul_exp_primeZeta hs']
  change (s - 1) * GaloisForLFunctions.squarefreePartition s /
      squarefreeCarlemanDet s =
    (s - 1) * Complex.exp (coronaPrimeZeta s)
  rw [squarefreePartition_eq_carleman_mul_exp hs']
  field_simp [squarefreeCarlemanDet_ne_zero]

private theorem tendstoLocallyUniformlyOn_const_index
    {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {φ : Filter ι} {s : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ι => g) g φ s := by
  intro u hu x hx
  exact ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

theorem tendstoLocallyUniformlyOn_poleClearedFirstTraceSourceApprox :
    TendstoLocallyUniformlyOn poleClearedFirstTraceSourceApprox
      poleClearedFirstTraceSourceLimit atTop farHalf := by
  have hrcont : ContinuousOn poleFactorSqrtCayleyLimit farHalf :=
    tendstoLocallyUniformlyOn_poleFactorSqrtApprox.continuousOn
      (Frequently.of_forall fun n =>
        (analyticOnNhd_poleFactorSqrtApprox_rightHalf n).continuousOn.mono
          farHalf_subset_rightHalf)
  have hLcont : ContinuousOn (LSeries squarefreeConvolutionHalf) farHalf :=
    analyticOnNhd_LSeries_squarefreeConvolutionHalf.continuousOn
  have hdencont : ContinuousOn squarefreeCarlemanHalfDet farHalf :=
    analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf.continuousOn.mono
      farHalf_subset_rightHalf
  have hnum := tendstoLocallyUniformlyOn_poleFactorSqrtApprox.mul₀
    tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums hrcont hLcont
  have hden : TendstoLocallyUniformlyOn
      (fun _ : ℕ => squarefreeCarlemanHalfDet) squarefreeCarlemanHalfDet atTop farHalf :=
    tendstoLocallyUniformlyOn_const_index squarefreeCarlemanHalfDet
  have hdiv := hnum.div₀ hden (hrcont.mul hLcont) hdencont
    (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)
  convert hdiv using 1
  · ext N s
    rfl
  · ext s
    rfl

/-- Local boundedness of the one explicit arithmetic approximation sequence. -/
def PoleClearedFirstTraceSourceLocallyBounded : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R, ‖poleClearedFirstTraceSourceApprox N w‖ ≤ C

/-- **[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]** Local boundedness of the explicit source
sequence forces the first parity rung. -/
theorem rhLadder_one_of_poleClearedFirstTraceSourceLocallyBounded
    (hloc : PoleClearedFirstTraceSourceLocallyBounded) : RHLadder 1 := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N => (analyticOnNhd_poleClearedFirstTraceSourceApprox_rightHalf N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        tendstoLocallyUniformlyOn_poleClearedFirstTraceSourceApprox.tendsto_at hs⟩)
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  refine ⟨G, hGdiff.analyticOnNhd isOpen_rightHalf, ?_⟩
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      (tendstoLocallyUniformlyOn_poleClearedFirstTraceSourceApprox.tendsto_at hs)
  let H : ℂ → ℂ := fun s => G s ^ 2 - poleClearedFirstTraceExponentialContinuation s
  have hHana : AnalyticOnNhd ℂ H rightHalf :=
    ((hGdiff.analyticOnNhd isOpen_rightHalf).pow 2).sub
      analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hmem : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf := isOpen_farHalf.mem_nhds two_mem_farHalf
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
