import GaloisForLFunctions.RHTower.CHMDRealApertureDomain
import GaloisForLFunctions.RHTower.CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces

/-!
# The maximal supported graph is the completed aperture core

Bounded mollification, weak Hilbert compactness and clipping admit every
supported maximal graph vector. The common weighted Fourier domain removes
the temporary enlargement of the aperture used during smoothing. In
particular, the completed aperture graph is stable under nodal truncations.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace Convolution ContDiff
open GaloisForLFunctions.RHTower

set_option autoImplicit false
noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDPolar CHMDClosedJump WeilOneSided
open GaloisForLFunctions.HTGeometry


/-- Graph-bounded approximants with convergent sources stay in any closed
graph subspace. The literal source projection identifies the weak limit. -/
theorem mem_closed_graph_submodule_of_bounded_source_approx
    (S : Submodule ℝ SourceGraph) [CompleteSpace S]
    (p : SourceGraph) (u : ℕ → SourceGraph) (hu : ∀ n, u n ∈ S)
    (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M)
    (hs : Tendsto (fun n => (u n).val.fst) atTop (𝓝 p.val.fst)) : p ∈ S := by
  obtain ⟨w, φ, hφ, hw⟩ := exists_real_weak_subseq u M hM
  have hwS : w ∈ S := by
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
    intro y hy
    have hzero : ∀ n, ⟪u (φ n), y⟫_ℝ = 0 :=
      fun n => S.inner_right_of_mem_orthogonal (hu (φ n)) hy
    exact tendsto_nhds_unique (hw y) (by simp only [hzero]; exact tendsto_const_nhds)
  have hwp : w = p := by
    apply source_projection_injective
    apply ext_inner_right ℝ
    intro y
    have hwsource : Tendsto (fun n => ⟪(u (φ n)).val.fst, y⟫_ℝ)
        atTop (𝓝 ⟪w.val.fst, y⟫_ℝ) := by
      change Tendsto (fun n => ⟪sourceMap (u (φ n)), y⟫_ℝ)
        atTop (𝓝 ⟪sourceMap w, y⟫_ℝ)
      simpa only [ContinuousLinearMap.adjoint_inner_right] using hw (sourceMap.adjoint y)
    exact tendsto_nhds_unique hwsource
      ((hs.comp hφ.tendsto_atTop).inner (tendsto_const_nhds (x := y)))
  rwa [← hwp]

private def largerAperture (a : SuzukiPositiveAperture) : SuzukiPositiveAperture :=
  ⟨a.1 + 1, by linarith [a.property]⟩

private theorem smooth_contDiff_infty {v : ℝ → ℝ} (h2 : MemLp v 2 volume) (n : ℕ) :
    ContDiff ℝ ∞ (smooth v n) :=
  (mollifier_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (show ContDiff ℝ ∞ (CHMDDoobGraph.mollifier n) from (narrowBump n).contDiff_normed)
    (h2.locallyIntegrable (by norm_num))

private theorem mollifier_support_abs_le (n : ℕ) {x : ℝ} (hx : CHMDDoobGraph.mollifier n x ≠ 0) :
    |x| ≤ 1 / 4 := by
  have hx' : x ∈ Function.support ((narrowBump n).normed volume) := hx
  rw [(narrowBump n).support_normed_eq] at hx'
  have hdist : |x| < 1 / (4 * ((n : ℝ) + 1)) := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, narrowBump] using hx'
  have hden : 1 / (4 * ((n : ℝ) + 1)) ≤ (1 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  exact hdist.le.trans hden

private theorem smooth_zero_off_enlarged {a : ℝ} {v : ℝ → ℝ}
    (hv : ∀ x ∉ Icc (-a) a, v x = 0) (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (-(a + 1 / 2)) (a + 1 / 2)) : smooth v n x = 0 := by
  change (∫ t, CHMDDoobGraph.mollifier n t * v (x - t)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : CHMDDoobGraph.mollifier n t = 0
  · simp only [ht, zero_mul, Pi.zero_apply]
  · have hxt : x - t ∉ Icc (-a) a := by
      intro hxt
      have ht' := abs_le.mp (mollifier_support_abs_le n ht)
      apply hx
      constructor <;> linarith only [hxt.1, hxt.2, ht'.1, ht'.2]
    simp only [hv (x - t) hxt, mul_zero, Pi.zero_apply]

private def smoothedPhysicalCore (a : SuzukiPositiveAperture) (v : ℝ → ℝ)
    (hv : MemLp v 2 volume) (hs : ∀ x ∉ Icc (-a.1) a.1, v x = 0) (n : ℕ) :
    SuzukiRestrictedWeilCore (largerAperture a).1 where
  toFun := phiDoobTest (smooth v n)
  smooth := contDiff_riemannKernelReal.mul (smooth_contDiff_infty hv n)
  supportRadius := a.1 + 1 / 2
  supportRadius_nonneg := by linarith [a.property]
  supportRadius_lt_aperture := by dsimp [largerAperture]; linarith
  support_subset := by
    intro x hx
    by_contra hnot
    exact hx (by
      dsimp [phiDoobTest]
      rw [smooth_zero_off_enlarged hs n hnot, mul_zero])

private theorem smoothLift_mem_largerAperture (a : SuzukiPositiveAperture)
    (v : ℝ → ℝ) (hv : MemLp v 2 volume) (hc : HasCompactSupport v)
    (hs : ∀ x ∉ Icc (-a.1) a.1, v x = 0) (n : ℕ) :
    compactLift (smooth v n) (smooth_contDiff hv n) (smooth_compact hc n) ∈
      apertureGraphCompletion (largerAperture a) := by
  apply (apertureGraphCore (largerAperture a)).le_topologicalClosure
  refine ⟨smoothedPhysicalCore a v hv hs n, ?_⟩
  exact (testLift_phi (smooth v n) (smooth_contDiff hv n) (smooth_compact hc n)).symm

/-- A bounded maximal source supported in an aperture belongs to a larger
smooth aperture completion. No convergence of the smoothed edges is assumed. -/
private theorem bounded_supported_mem_largerAperture (a : SuzukiPositiveAperture)
    (v : ℝ → ℝ) (hv : Measurable v) (hc : HasCompactSupport v)
    (hs : MemLp v 2 massMeasure) (hd : MemLp (difference v) 2 edgeMeasure)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M)
    (hvs : ∀ x ∉ Icc (-a.1) a.1, v x = 0) :
    ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v hs hd ∈
      apertureGraphCompletion (largerAperture a) := by
  have hv2 := bounded_compact_memLp_volume hv hc hM hb
  let u : ℕ → SourceGraph := fun n =>
    compactLift (smooth v n) (smooth_contDiff hv2 n) (smooth_compact hc n)
  obtain ⟨C, hC, hθ, _⟩ := theta_global_and_exponential_bound
  let B := (∫ _ : ℝ, M ^ 2 ∂massMeasure) +
    (C ^ 2 * stationaryEnergy v + ∫ _ : ℝ × ℝ, 4 * M ^ 2 ∂Measure.sum primeMeasure)
  have hnorm (n : ℕ) : ‖u n‖ ≤ Real.sqrt B := by
    have hh := compactLift_norm_sq_bound (smooth_contDiff hv2 n) (smooth_compact hc n)
      hM (smooth_bound hM hb n) hC hθ (stationaryEnergy_smooth_le hv hc hd hM hb n)
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hh
  apply mem_closed_graph_submodule_of_bounded_source_approx
    (apertureGraphCompletion (largerAperture a)) _ u
    (fun n => smoothLift_mem_largerAperture a v hv2 hc hvs n) (Real.sqrt B) hnorm
  apply toLp_tendsto_of_sq_dom
    (fun n => compact_memLp_mass (smooth_contDiff hv2 n).continuous (smooth_compact hc n))
    hs (integrable_const (4 * M ^ 2))
  · intro n
    filter_upwards [] with x
    have ha : |smooth v n x - v x| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [smooth_bound hM hb n x, hb x])
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr ha
  · exact smooth_tendsto_ae hv2

/-- Physical aperture support is equivalent to support of the inverse-Doob
coordinate, since theta is strictly positive and the measures are equivalent. -/
theorem graphPhysicalSource_supported_iff (a : ℝ) (p : SourceGraph) :
    suzukiCutoff a (graphPhysicalSource p) = graphPhysicalSource p ↔
      ∀ᵐ x ∂massMeasure, x ∉ Icc (-a) a → p.val.fst x = 0 := by
  constructor
  · intro hs
    have hz := suzukiCutoff_ae_eq_zero_off a (graphPhysicalSource p)
    rw [hs] at hz
    apply (withDensity_absolutelyContinuous volume _).ae_le
    filter_upwards [hz, graphPhysicalSource_ae p] with x hx hp
    intro hnot
    have he : phiDoobTest p.val.fst x = 0 := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_zero] using hp.symm.trans (hx hnot)
    exact (mul_eq_zero.mp he).resolve_left (riemannKernelReal_pos x).ne'
  · intro hs
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc (graphPhysicalSource p),
      graphPhysicalSource_ae p, volume_absolutelyContinuous_mass.ae_le hs] with x hc hp hz
    rw [hc]
    by_cases hx : x ∈ Icc (-a) a
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hp]
      simp only [phiDoobTest, hz hx, mul_zero, Complex.ofReal_zero]

private theorem supported_mem_largerAperture (a : SuzukiPositiveAperture) (p : SourceGraph)
    (hs : ∀ᵐ x ∂massMeasure, x ∉ Icc (-a.1) a.1 → p.val.fst x = 0) :
    p ∈ apertureGraphCompletion (largerAperture a) := by
  apply (isClosed_apertureGraphCompletion (largerAperture a)).mem_of_tendsto
    (truncate_tendsto massMeasure edgeMeasure left right nonsingular_left nonsingular_right p)
  refine Eventually.of_forall fun n => ?_
  let q := truncate massMeasure edgeMeasure left right nonsingular_left nonsingular_right p n
  let v : ℝ → ℝ := (Icc (-a.1) a.1).indicator (clip n ∘ p.val.fst)
  have hv : Measurable v :=
    ((lipschitz_clip n).continuous.measurable.comp
      (Lp.stronglyMeasurable p.val.fst).measurable).indicator measurableSet_Icc
  have hvs : ∀ x ∉ Icc (-a.1) a.1, v x = 0 := fun x hx => indicator_of_notMem hx _
  have heq : q.val.fst =ᵐ[massMeasure] v := by
    filter_upwards [contract_source_ae massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right p (lipschitz_clip n) (clip_zero n), hs] with x hq hx
    change q.val.fst x = _ at hq
    rw [hq]
    by_cases hxa : x ∈ Icc (-a.1) a.1
    · exact (indicator_of_mem hxa _).symm
    · rw [hvs x hxa, Function.comp_apply, hx hxa, clip_zero]
  have h2 : MemLp v 2 massMeasure := (memLp_congr_ae heq).mp (Lp.memLp q.val.fst)
  have hed : q.val.snd =ᵐ[edgeMeasure] difference v := by
    filter_upwards [q.property, nonsingular_left.ae heq, nonsingular_right.ae heq]
      with e hq hl hr
    simpa only [difference, hl, hr] using hq
  have hd : MemLp (difference v) 2 edgeMeasure := (memLp_congr_ae hed).mp (Lp.memLp q.val.snd)
  have hc : HasCompactSupport v := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro x hx
    by_contra hnot
    exact hx (hvs x hnot)
  have hb : ∀ x, |v x| ≤ (n : ℝ) := by
    intro x
    by_cases hx : x ∈ Icc (-a.1) a.1
    · rw [show v x = clip n (p.val.fst x) from indicator_of_mem hx _]
      exact abs_clip_le n _
    · rw [hvs x hx, abs_zero]
      exact Nat.cast_nonneg n
  have hp : ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v h2 hd = q := by
    apply source_projection_injective
    exact Lp.ext (h2.coeFn_toLp.trans heq.symm)
  change q ∈ apertureGraphCompletion (largerAperture a)
  rw [← hp]
  exact bounded_supported_mem_largerAperture a v hv hc h2 hd n (Nat.cast_nonneg n) hb hvs

/-- The completed smooth aperture core is exactly the maximal graph with
physical support in the closed aperture, including its boundary. -/
theorem mem_apertureGraphCompletion_iff_supported (a : SuzukiPositiveAperture)
    (p : SourceGraph) :
    p ∈ apertureGraphCompletion a ↔
      suzukiCutoff a.1 (graphPhysicalSource p) = graphPhysicalSource p := by
  constructor
  · exact physicalSource_supported_of_mem_apertureGraphCompletion a
  · intro hs
    have hpb := supported_mem_largerAperture a p ((graphPhysicalSource_supported_iff a.1 p).mp hs)
    let pb : apertureGraphCompletion (largerAperture a) := ⟨p, hpb⟩
    let qb := (apertureGraphWeilEquiv (largerAperture a) pb).val
    have hphysical : ccmArchimedeanFormEmbedding (largerAperture a) qb = graphPhysicalSource p :=
      apertureGraphWeilEquiv_physical (largerAperture a) pb
    have hqa : qb.val ∈ (ccmArchimedeanSupportDefect a).ker := by
      rw [LinearMap.mem_ker]
      change ccmArchimedeanFourierToTime qb.val -
        suzukiCutoff a.1 (ccmArchimedeanFourierToTime qb.val) = 0
      change ccmArchimedeanFormEmbedding (largerAperture a) qb -
        suzukiCutoff a.1 (ccmArchimedeanFormEmbedding (largerAperture a) qb) = 0
      rw [hphysical, hs, sub_self]
    let qa : CCMArchimedeanFormDomain a := ⟨qb.val, hqa⟩
    have hqaPhysical : ccmArchimedeanFormEmbedding a qa = graphPhysicalSource p := hphysical
    have hreal : ∀ᵐ x ∂volume, (ccmArchimedeanFormEmbedding a qa x).im = 0 := by
      rw [hqaPhysical]
      filter_upwards [graphPhysicalSource_ae p] with x hx
      rw [hx, Complex.ofReal_im]
    obtain ⟨p', ⟨hp', _⟩, _⟩ := existsUnique_real_aperture_lift a qa hreal
    have heq : p'.val = p := graphPhysicalSource_injective (hp'.trans hqaPhysical)
    exact heq ▸ p'.property

/-- The quotient norm controls every maximal source in a fixed aperture,
without an additional core-closure premise. -/
theorem exists_supported_aperture_quotient_lower_bound (a : SuzukiPositiveAperture) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : SourceGraph,
      suzukiCutoff a.1 (graphPhysicalSource p) = graphPhysicalSource p →
        c * ‖p‖ ≤ ‖signedQuotientMk p‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_aperture_quotient_lower_bound a
  exact ⟨c, hc, fun p hp => hbound p ((mem_apertureGraphCompletion_iff_supported a p).mpr hp)⟩

/-- Positive-part truncation preserves the completed aperture domain. -/
theorem posGraph_mem_apertureGraphCompletion (a : SuzukiPositiveAperture)
    {p : SourceGraph} (hp : p ∈ apertureGraphCompletion a) :
    posGraph p ∈ apertureGraphCompletion a := by
  apply (mem_apertureGraphCompletion_iff_supported a (posGraph p)).mpr
  apply (graphPhysicalSource_supported_iff a.1 (posGraph p)).mpr
  have hs := (graphPhysicalSource_supported_iff a.1 p).mp
    (physicalSource_supported_of_mem_apertureGraphCompletion a hp)
  filter_upwards [hs, posGraph_fst_ae p] with x hx hpos
  intro hnot
  rw [hpos, hx hnot, posFun_zero]

/-- Negative-part truncation preserves the completed aperture domain. -/
theorem negGraph_mem_apertureGraphCompletion (a : SuzukiPositiveAperture)
    {p : SourceGraph} (hp : p ∈ apertureGraphCompletion a) :
    negGraph p ∈ apertureGraphCompletion a := by
  apply (mem_apertureGraphCompletion_iff_supported a (negGraph p)).mpr
  apply (graphPhysicalSource_supported_iff a.1 (negGraph p)).mpr
  have hs := (graphPhysicalSource_supported_iff a.1 p).mp
    (physicalSource_supported_of_mem_apertureGraphCompletion a hp)
  filter_upwards [hs, negGraph_fst_ae p] with x hx hneg
  intro hnot
  rw [hneg, hx hnot, negFun_zero]

/-- Modulus preserves the completed aperture domain. -/
theorem absGraph_mem_apertureGraphCompletion (a : SuzukiPositiveAperture)
    {p : SourceGraph} (hp : p ∈ apertureGraphCompletion a) :
    absGraph p ∈ apertureGraphCompletion a := by
  rw [← posGraph_add_negGraph]
  exact (apertureGraphCompletion a).add_mem
    (posGraph_mem_apertureGraphCompletion a hp) (negGraph_mem_apertureGraphCompletion a hp)


end RHTower
