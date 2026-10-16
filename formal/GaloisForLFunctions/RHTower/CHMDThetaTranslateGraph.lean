import GaloisForLFunctions.RHTower.CHMDThetaTranslateMass
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization

/-!
# Theta translations in the complete arithmetic jump graph

Small theta translations enter the actual maximal graph as strong limits of
compact tests. Exact preservation of signed difference energies supplies the
edge convergence; no prime truncation or sign premise is inserted.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDThetaTranslate
open CHMDDoobGraph CHMDTranslation CHMDClosedJump

def cutSource (n : ℕ) : ℝ → ℝ := phiDoobTest (cutoff n)

theorem cutSource_contDiff (n : ℕ) : ContDiff ℝ 2 (cutSource n) :=
  contDiff_phiDoobTest (cutoff_contDiff n)

theorem cutSource_compact (n : ℕ) : HasCompactSupport (cutSource n) :=
  hasCompactSupport_phiDoobTest (cutoff_hasCompactSupport n)

def approx (a : ℝ) (n : ℕ) : SourceGraph :=
  testLift (translate (cutSource n) a) (contDiff_translate (cutSource_contDiff n) a)
    (compact_translate (cutSource_compact n) a)

theorem testLift_congr {f g : ℝ → ℝ} (h : f = g)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    testLift f hf hc = testLift g hg hgc := by subst g; rfl

theorem approx_zero (n : ℕ) : approx 0 n = cutoffLift n := by
  have h : CHMDTranslation.translate (cutSource n) 0 = cutSource n := by
    funext x; simp only [CHMDTranslation.translate, sub_zero]
  exact (testLift_congr h _ _ _ _).trans
    (testLift_phi (cutoff n) (cutoff_contDiff n) (cutoff_hasCompactSupport n))

theorem approx_source_function (a : ℝ) (n : ℕ) (x : ℝ) :
    phiDoobInv (translate (cutSource n) a) x = ratio a x * cutoff n (x-a) := by
  unfold phiDoobInv CHMDTranslation.translate cutSource phiDoobTest ratio
  ring

theorem approx_source_tendsto {a : ℝ} (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    Tendsto (fun n => (approx a n).val.fst) atTop (𝓝 ((memLp_ratio ha).toLp (ratio a))) := by
  apply toLp_tendsto_of_sq_dom
    (fun n => compact_memLp_mass (contDiff_phiDoobInv
      (contDiff_translate (cutSource_contDiff n) a)).continuous
      (hasCompactSupport_phiDoobInv (compact_translate (cutSource_compact n) a)))
    (memLp_ratio ha) (memLp_ratio ha).integrable_sq
  · intro n
    refine Eventually.of_forall fun x => ?_
    rw [approx_source_function]
    have hr : 0 ≤ ratio a x := (div_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _)).le
    have h0 : 0 ≤ ratio a x * cutoff n (x-a) := mul_nonneg hr (cutoff_nonneg n _)
    have h1 : ratio a x * cutoff n (x-a) ≤ ratio a x :=
      mul_le_of_le_one_right hr (cutoff_le_one n _)
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  · refine Eventually.of_forall fun x => ?_
    simp only [approx_source_function]
    simpa only [mul_one] using (cutoff_tendsto (x-a)).const_mul (ratio a x)

theorem approx_difference_energy (a : ℝ) (m n : ℕ) :
    sourceEnergy (approx a m - approx a n) = sourceEnergy (cutoffLift m - cutoffLift n) := by
  rw [← approx_zero m, ← approx_zero n]
  unfold approx
  rw [← testLift_sub, ← testLift_sub, testLift_energy, testLift_energy]
  change markovEnergy (fun x => (translate (cutSource m-cutSource n) a x : ℂ)) =
    markovEnergy (fun x => (translate (cutSource m-cutSource n) 0 x : ℂ))
  rw [markovEnergy_translate, markovEnergy_translate]

theorem exists_limit {a : ℝ} (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ∃ p : SourceGraph, Tendsto (approx a) atTop (𝓝 p) := by
  apply cauchySeq_tendsto_of_complete
  exact cauchySeq_of_energy_transfer (approx a) cutoffLift
    cutoffLift_tendsto_constant.cauchySeq (approx_source_tendsto ha).cauchySeq
    (approx_difference_energy a)

def lift (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) : SourceGraph := (exists_limit ha).choose

theorem approx_tendsto (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    Tendsto (approx a) atTop (𝓝 (lift a ha)) := (exists_limit ha).choose_spec

theorem lift_source (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (lift a ha).val.fst = (memLp_ratio ha).toLp (ratio a) :=
  tendsto_nhds_unique (sourceMap.continuous.tendsto _ |>.comp (approx_tendsto a ha))
    (approx_source_tendsto ha)

theorem lift_source_ae (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (lift a ha).val.fst =ᵐ[massMeasure] ratio a := by
  rw [lift_source]
  exact (memLp_ratio ha).coeFn_toLp

theorem lift_zero (ha : 1 < 2 * Real.exp (-2 * |(0 : ℝ)|)) : lift 0 ha = constantLift 1 := by
  apply tendsto_nhds_unique (approx_tendsto 0 ha)
  rw [show approx 0 = cutoffLift from funext approx_zero]
  exact cutoffLift_tendsto_constant

/-- Mixed compact pairing sees just the shifted hyperbolic moment. -/
theorem pair_lift_test (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourcePair (lift a ha) (testLift f hf hc) = -coshHalfMoment (translate f (-a)) := by
  let g := translate f (-a)
  have hg : ContDiff ℝ 2 g := contDiff_translate hf (-a)
  have hgc : HasCompactSupport g := compact_translate hc (-a)
  have hback : translate g a = f := by funext x; simp [g, CHMDTranslation.translate]
  have he (n : ℕ) : sourcePair (approx a n) (testLift f hf hc) =
      sourcePair (cutoffLift n) (testLift g hg hgc) := by
    have hh := sourcePair_translate (cutSource n) g (cutSource_contDiff n) hg (cutSource_compact n) hgc a
    have hb := testLift_congr hback (contDiff_translate hg a) hf (compact_translate hgc a) hc
    have hk : testLift (cutSource n) (cutSource_contDiff n) (cutSource_compact n) = cutoffLift n :=
      testLift_phi (cutoff n) (cutoff_contDiff n) (cutoff_hasCompactSupport n)
    rw [hb, hk] at hh
    exact hh
  have hleft := continuous_sourcePair.continuousAt.tendsto.comp
    ((approx_tendsto a ha).prodMk_nhds (tendsto_const_nhds (x := testLift f hf hc)))
  have hright := continuous_sourcePair.continuousAt.tendsto.comp
    (cutoffLift_tendsto_constant.prodMk_nhds (tendsto_const_nhds (x := testLift g hg hgc)))
  have hi : sourcePair (lift a ha) (testLift f hf hc) =
      sourcePair (constantLift 1) (testLift g hg hgc) :=
    tendsto_nhds_unique hleft (by simpa only [Function.comp_def, he] using hright)
  rw [hi, sourcePair_ground]
  congr 1
  rw [L2.inner_def]
  change (∫ x, (testLift g hg hgc).val.fst x * (constantLift 1).val.fst x ∂massMeasure) =
    coshHalfMoment g
  unfold coshHalfMoment
  change (∫ x, (testLift g hg hgc).val.fst x * (constantLift 1).val.fst x
    ∂volume.withDensity (fun x => ENNReal.ofReal (massDensity x))) = _
  rw [integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  have h1 := (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
  have h2 := testLift_source g hg hgc
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq h1,
    volume_absolutelyContinuous_mass.ae_eq h2] with x hx hy
  change (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x = 1 at hx
  change massDensity x * ((testLift g hg hgc).val.fst x *
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x) = _
  rw [hx, hy]
  dsimp only [massDensity, phiDoobInv]
  field_simp [(riemannKernelReal_pos x).ne']

end RHTower.CHMDThetaTranslate
