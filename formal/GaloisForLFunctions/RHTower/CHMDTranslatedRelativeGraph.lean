import GaloisForLFunctions.RHTower.CHMDThetaTranslateGraph
import GaloisForLFunctions.RHTower.CHMDBulkCutoffGraph

/-!
# Small translations of theta-relative sources in the actual graph

Theta domination gives the translated source coordinate in L2. Exact arithmetic
translation invariance transfers Cauchy control of signed differences; together
these give strong convergence of the complete graph, including every prime edge.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDTranslation CHMDClosedJump WeilSpectral

theorem translated_relative_memLp {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) {a : ℝ}
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    MemLp (phiDoobInv (translate f a)) 2 massMeasure := by
  apply ((CHMDThetaTranslate.memLp_ratio ha).const_mul M).of_le
    (continuous_phiDoobInv (continuous_translate hf a)).aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hr : 0 ≤ CHMDThetaTranslate.ratio a x :=
    (div_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _)).le
  change |phiDoobInv (CHMDTranslation.translate f a) x| ≤ |M * CHMDThetaTranslate.ratio a x|
  rw [abs_of_nonneg (mul_nonneg hM hr)]
  simpa only [phiDoobInv, CHMDTranslation.translate, abs_div,
    abs_of_pos (riemannKernelReal_pos x), CHMDThetaTranslate.ratio, mul_div_assoc] using
    div_le_div_of_nonneg_right (hb (x-a)) (riemannKernelReal_pos x).le

def translatedApprox (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (a : ℝ) (n : ℕ) : SourceGraph :=
  testLift (translate (truncTest f n) a) (contDiff_translate (contDiff_truncTest hf n) a)
    (compact_translate (hasCompactSupport_truncTest f n) a)

theorem translatedApprox_source_function (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) :
    phiDoobInv (translate (truncTest f n) a) x =
      phiDoobInv (translate f a) x * bulkCutoff n (x-a) := by
  unfold phiDoobInv CHMDTranslation.translate truncTest
  ring

theorem translatedApprox_source_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) {a : ℝ}
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    Tendsto (fun n => (translatedApprox f hf a n).val.fst) atTop
      (𝓝 ((translated_relative_memLp hf.continuous hM hb ha).toLp (phiDoobInv (translate f a)))) := by
  apply toLp_tendsto_of_sq_dom
    (fun n => compact_memLp_mass (contDiff_phiDoobInv
      (contDiff_translate (contDiff_truncTest hf n) a)).continuous
      (hasCompactSupport_phiDoobInv (compact_translate (hasCompactSupport_truncTest f n) a)))
    (translated_relative_memLp hf.continuous hM hb ha)
    (translated_relative_memLp hf.continuous hM hb ha).integrable_sq
  · intro n
    refine Eventually.of_forall fun x => ?_
    rw [translatedApprox_source_function]
    have h0 := bulkCutoff_nonneg (n : ℝ) (x-a)
    have h1 := bulkCutoff_le_one (n : ℝ) (x-a)
    have hk : (bulkCutoff n (x-a)-1)^2 ≤ 1 := by
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    calc
      _ = (phiDoobInv (translate f a) x)^2 * (bulkCutoff n (x-a)-1)^2 := by ring
      _ ≤ (phiDoobInv (translate f a) x)^2 * 1 :=
        mul_le_mul_of_nonneg_left hk (sq_nonneg _)
      _ = _ := mul_one _
  · exact Eventually.of_forall fun x => by
      simpa only [translatedApprox_source_function, mul_one] using
        (bulkCutoff_nat_tendsto (x-a)).const_mul (phiDoobInv (translate f a) x)

theorem translatedApprox_difference_energy (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (a : ℝ) (m n : ℕ) :
    sourceEnergy (translatedApprox f hf a m - translatedApprox f hf a n) =
      sourceEnergy (bulkTestLift f hf m - bulkTestLift f hf n) := by
  unfold translatedApprox bulkTestLift
  rw [← testLift_sub, ← testLift_sub, testLift_energy, testLift_energy]
  change markovEnergy (fun x => (translate (truncTest f m-truncTest f n) a x : ℂ)) = _
  exact markovEnergy_translate (truncTest f m-truncTest f n) a

theorem bulkTestLift_tendsto_of_source {f : ℝ → ℝ} {p : SourceGraph}
    (hf : ContDiff ℝ 2 f) (hl : ∃ A, LipschitzWith A f)
    (hb : ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) :
    Tendsto (bulkTestLift f hf) atTop (𝓝 p) := by
  obtain ⟨A, hA⟩ := hl
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left
    ((abs_nonneg (f 0)).trans (hM 0)) (riemannKernelReal_pos 0)
  have he : p = relativeLift f hA hM0 hM := by
    apply source_projection_injective
    exact Lp.ext (hp.trans (relativeLift_source_ae f hA hM0 hM).symm)
  rw [he]
  exact bulkTestLift_tendsto hf hA hM0 hM

/-- A literal translated source and its strong graph approximation, with no assumed edge bound. -/
theorem exists_graph_translate {f : ℝ → ℝ} {p : SourceGraph}
    (hf : ContDiff ℝ 2 f) (hl : ∃ A, LipschitzWith A f)
    (hb : ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ∃ u : SourceGraph, Tendsto (translatedApprox f hf a) atTop (𝓝 u) ∧
      u.val.fst =ᵐ[massMeasure] phiDoobInv (translate f a) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left
    ((abs_nonneg (f 0)).trans (hM 0)) (riemannKernelReal_pos 0)
  have hs := translatedApprox_source_tendsto hf hM0 hM ha
  have hbase := bulkTestLift_tendsto_of_source hf hl ⟨M, hM⟩ hp
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_energy_transfer (translatedApprox f hf a) (bulkTestLift f hf)
      hbase.cauchySeq hs.cauchySeq (translatedApprox_difference_energy f hf a))
  refine ⟨u, hu, ?_⟩
  have he := tendsto_nhds_unique
    (sourceMap.continuous.tendsto _ |>.comp hu) hs
  change u.val.fst = _ at he
  rw [he]
  exact (translated_relative_memLp hf.continuous hM0 hM ha).coeFn_toLp

theorem graph_translate_pair_test {f : ℝ → ℝ} {p u : SourceGraph}
    (hf : ContDiff ℝ 2 f) (hl : ∃ A, LipschitzWith A f)
    (hb : ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) (a : ℝ)
    (hu : Tendsto (translatedApprox f hf a) atTop (𝓝 u))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    sourcePair u (testLift g hg hc) = sourcePair p
      (testLift (translate g (-a)) (contDiff_translate hg (-a)) (compact_translate hc (-a))) := by
  let b := translate g (-a)
  have hbd : ContDiff ℝ 2 b := contDiff_translate hg (-a)
  have hbc : HasCompactSupport b := compact_translate hc (-a)
  have hback : translate b a = g := by funext x; simp [b, CHMDTranslation.translate]
  have he (n : ℕ) : sourcePair (translatedApprox f hf a n) (testLift g hg hc) =
      sourcePair (bulkTestLift f hf n) (testLift b hbd hbc) := by
    have h := sourcePair_translate (truncTest f n) b (contDiff_truncTest hf n) hbd
      (hasCompactSupport_truncTest f n) hbc a
    rw [CHMDThetaTranslate.testLift_congr hback _ hg _ hc] at h
    exact h
  have hleft := continuous_sourcePair.continuousAt.tendsto.comp
    (hu.prodMk_nhds (tendsto_const_nhds (x := testLift g hg hc)))
  have hright := continuous_sourcePair.continuousAt.tendsto.comp
    ((bulkTestLift_tendsto_of_source hf hl hb hp).prodMk_nhds
      (tendsto_const_nhds (x := testLift b hbd hbc)))
  exact tendsto_nhds_unique hleft (by simpa only [Function.comp_def, he] using hright)

end RHTower.CHMDDoobGraph
