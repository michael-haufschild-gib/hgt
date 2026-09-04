import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfVitaliCriterion
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Cesàro source criterion for the squarefree convolution half

The canonical convolution-half Dirichlet polynomials fail raw local boundedness inside the Euler
wall. Point-Hermite corrections are also closed. This module tests a genuinely nonlocal successor:
Cesàro averaging over all earlier arithmetic cutoffs.

The averages are entire and retain the canonical Euler half-germ by compact-open Cesàro
convergence. After the existing pole-factor and Carleman transports, local boundedness of this one
explicit source family implies `RHLadder 1`. No such bound or RH conclusion is asserted here.
-/

open Complex Filter Metric Set Topology
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cesàro averages of the canonical convolution-half Dirichlet polynomials. -/
def squarefreeHalfCesaroSum (N : ℕ) (s : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ M ∈ Finset.range N, squarefreeHalfDirichletPartialSum M s

theorem analyticOnNhd_squarefreeHalfCesaroSum (N : ℕ) :
    AnalyticOnNhd ℂ (squarefreeHalfCesaroSum N) Set.univ := by
  unfold squarefreeHalfCesaroSum
  exact analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_sum _ fun M _ =>
      analyticOnNhd_squarefreeHalfDirichletPartialSum M)

/-- Cesàro averaging preserves the exact canonical half on the Euler chamber, locally uniformly. -/
theorem tendstoLocallyUniformlyOn_squarefreeHalfCesaroSum :
    TendstoLocallyUniformlyOn squarefreeHalfCesaroSum
      (LSeries squarefreeConvolutionHalf) atTop farHalf := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_farHalf]
  intro K hKfar hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hDcont : ∀ N, ContinuousOn (squarefreeHalfDirichletPartialSum N) K :=
    fun N => (analyticOnNhd_squarefreeHalfDirichletPartialSum N).continuousOn.mono
      (Set.subset_univ K)
  have hLcont : ContinuousOn (LSeries squarefreeConvolutionHalf) K :=
    analyticOnNhd_LSeries_squarefreeConvolutionHalf.continuousOn.mono hKfar
  have hU : TendstoUniformlyOn squarefreeHalfDirichletPartialSum
      (LSeries squarefreeConvolutionHalf) atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums.mono hKfar)
  let D : ℕ → C(K, ℂ) := fun N =>
    ⟨K.restrict (squarefreeHalfDirichletPartialSum N),
      (hDcont N).restrict⟩
  let L : C(K, ℂ) :=
    ⟨K.restrict (LSeries squarefreeConvolutionHalf), hLcont.restrict⟩
  have hrest : Tendsto D atTop (𝓝 L) := by
    simpa [D, L] using
      (hLcont.tendsto_restrict_iff_tendstoUniformlyOn hDcont).mpr hU
  have hces := hrest.cesaro_smul
  have hCcont : ∀ N, ContinuousOn (squarefreeHalfCesaroSum N) K :=
    fun N => (analyticOnNhd_squarefreeHalfCesaroSum N).continuousOn.mono
      (Set.subset_univ K)
  let C : ℕ → C(K, ℂ) := fun N =>
    ⟨K.restrict (squarefreeHalfCesaroSum N), (hCcont N).restrict⟩
  have havg :
      (fun N : ℕ => (N⁻¹ : ℝ) • ∑ M ∈ Finset.range N, D M) = C := by
    funext N
    ext z
    rw [ContinuousMap.smul_apply]
    let ev : C(K, ℂ) →+ ℂ :=
      { toFun := fun f => f z
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hsum :
        (∑ M ∈ Finset.range N, D M) z =
          ∑ M ∈ Finset.range N, (D M) z := by
      simp
    rw [hsum]
    simp only [D, C, ContinuousMap.coe_mk, Set.restrict_apply]
    rw [Complex.real_smul]
    rw [squarefreeHalfCesaroSum]
    push_cast
    rfl
  rw [havg] at hces
  exact (hLcont.tendsto_restrict_iff_tendstoUniformlyOn hCcont).mp
    (by simpa [C, L] using hces)

/-- Source-defined pole-cleared approximants using nonlocal Cesàro cutoff averaging. -/
def poleClearedFirstTraceCesaroApprox (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox N s * squarefreeHalfCesaroSum N s /
    squarefreeCarlemanHalfDet s

theorem analyticOnNhd_poleClearedFirstTraceCesaroApprox_rightHalf (N : ℕ) :
    AnalyticOnNhd ℂ (poleClearedFirstTraceCesaroApprox N) rightHalf := by
  exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf N).mul
    ((analyticOnNhd_squarefreeHalfCesaroSum N).mono (Set.subset_univ _)) |>.div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)

private theorem tendstoLocallyUniformlyOn_const_nat
    {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {s : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => g) g atTop s := by
  intro u hu x hx
  exact ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

/-- Pole-cleared Cesàro approximants retain the exact Euler-chamber source limit. -/
theorem tendstoLocallyUniformlyOn_poleClearedFirstTraceCesaroApprox :
    TendstoLocallyUniformlyOn poleClearedFirstTraceCesaroApprox
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
    tendstoLocallyUniformlyOn_squarefreeHalfCesaroSum hrcont hLcont
  have hden : TendstoLocallyUniformlyOn
      (fun _ : ℕ => squarefreeCarlemanHalfDet) squarefreeCarlemanHalfDet atTop farHalf :=
    tendstoLocallyUniformlyOn_const_nat squarefreeCarlemanHalfDet
  have hdiv := hnum.div₀ hden (hrcont.mul hLcont) hdencont
    (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)
  convert hdiv using 1
  · ext N s
    rfl
  · ext s
    rfl

/-- Local boundedness obligation for one explicit Cesàro-smoothed arithmetic sequence. -/
def PoleClearedFirstTraceCesaroLocallyBounded : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R, ‖poleClearedFirstTraceCesaroApprox N w‖ ≤ C

/-- **[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]** Local boundedness of the canonical Cesàro
approximants forces the first multiplicity rung. -/
theorem rhLadder_one_of_poleClearedFirstTraceCesaroLocallyBounded
    (hloc : PoleClearedFirstTraceCesaroLocallyBounded) : RHLadder 1 := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N =>
        (analyticOnNhd_poleClearedFirstTraceCesaroApprox_rightHalf N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        tendstoLocallyUniformlyOn_poleClearedFirstTraceCesaroApprox.tendsto_at hs⟩)
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  refine ⟨G, hGdiff.analyticOnNhd isOpen_rightHalf, ?_⟩
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      (tendstoLocallyUniformlyOn_poleClearedFirstTraceCesaroApprox.tendsto_at hs)
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
