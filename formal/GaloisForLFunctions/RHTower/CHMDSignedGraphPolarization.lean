import GaloisForLFunctions.RHTower.CHMDFullJumpCoreDensity
import GaloisForLFunctions.RHTower.CHMDTranslatedPrimitiveSource

/-!
# Signed polarization and energy-preserving completion

The original signed form polarizes continuously on the complete Doob graph.
Preserving energies of differences transfers Cauchy convergence as soon as the
actual source coordinates converge. No positivity of the signed form is used.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph

def edgeMap : SourceGraph →L[ℝ] Lp ℝ 2 edgeMeasure :=
  (WithLp.sndL 2 ℝ _ _).comp SourceGraph.subtypeL

def sourcePair (p q : SourceGraph) : ℝ :=
  ⟪edgeMap p, edgeMap q⟫_ℝ - ⟪sourceMap p, sourceMap q⟫_ℝ

theorem continuous_sourcePair : Continuous (fun p : SourceGraph × SourceGraph => sourcePair p.1 p.2) :=
  ((edgeMap.continuous.comp continuous_fst).inner (edgeMap.continuous.comp continuous_snd)).sub
    ((sourceMap.continuous.comp continuous_fst).inner (sourceMap.continuous.comp continuous_snd))

theorem sourcePair_self (p : SourceGraph) : sourcePair p p = sourceEnergy p := by
  simp only [sourcePair, real_inner_self_eq_norm_sq]
  rfl

theorem sourcePair_symm (p q : SourceGraph) : sourcePair p q = sourcePair q p := by
  unfold sourcePair
  rw [real_inner_comm (edgeMap p), real_inner_comm (sourceMap p)]

theorem sourcePair_add_left (p q r : SourceGraph) :
    sourcePair (p+q) r = sourcePair p r + sourcePair q r := by
  simp only [sourcePair, map_add, inner_add_left]
  ring

theorem sourcePair_smul_left (c : ℝ) (p q : SourceGraph) :
    sourcePair (c • p) q = c * sourcePair p q := by
  simp only [sourcePair, map_smul, real_inner_smul_left]
  ring

theorem sourcePair_sub_left (p q r : SourceGraph) :
    sourcePair (p-q) r = sourcePair p r - sourcePair q r := by
  simp only [sourcePair, map_sub, inner_sub_left]
  ring

theorem sourcePair_polarization (p q : SourceGraph) :
    sourcePair p q = (sourceEnergy (p+q) - sourceEnergy p - sourceEnergy q) / 2 := by
  simp only [← sourcePair_self, sourcePair_add_left, sourcePair_symm q (p+q),
    sourcePair_symm p (p+q), sourcePair_add_left]
  rw [sourcePair_symm q p]
  ring

theorem continuous_sourceEnergy : Continuous sourceEnergy := by
  simpa only [Function.comp_def, id_eq, sourcePair_self] using
    continuous_sourcePair.comp (continuous_id.prodMk continuous_id)

theorem sourcePair_ground (p : SourceGraph) :
    sourcePair (constantLift 1) p = -⟪(constantLift 1).val.fst, p.val.fst⟫_ℝ := by
  change ⟪(constantLift 1).val.snd, p.val.snd⟫_ℝ - _ = _
  rw [constantLift_edge, inner_zero_left, zero_sub]
  rfl

def testLift (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) : SourceGraph :=
  compactLift (phiDoobInv f) (contDiff_phiDoobInv hf) (hasCompactSupport_phiDoobInv hc)

theorem testLift_source (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (testLift f hf hc).val.fst =ᵐ[massMeasure] phiDoobInv f :=
  (compact_memLp_mass (contDiff_phiDoobInv hf).continuous (hasCompactSupport_phiDoobInv hc)).coeFn_toLp

theorem testLift_energy (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourceEnergy (testLift f hf hc) = markovEnergy (fun x => (f x : ℂ)) := by
  rw [testLift, sourceEnergy_compactLift]
  simp only [phiDoobTest_phiDoobInv]

theorem testLift_add (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    testLift (f+g) (hf.add hg) (hc.add hgc) = testLift f hf hc + testLift g hg hgc := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [testLift_source (f+g) _ _, testLift_source f hf hc, testLift_source g hg hgc,
    Lp.coeFn_add (testLift f hf hc).val.fst (testLift g hg hgc).val.fst] with x h0 h1 h2 h3
  change _ = ((testLift f hf hc).val.fst + (testLift g hg hgc).val.fst) x
  rw [h0, h3, Pi.add_apply, h1, h2]
  simp only [phiDoobInv, Pi.add_apply, add_div]

theorem testLift_sub (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    testLift (f-g) (hf.sub hg) (hc.sub hgc) = testLift f hf hc - testLift g hg hgc := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [testLift_source (f-g) _ _, testLift_source f hf hc, testLift_source g hg hgc,
    Lp.coeFn_sub (testLift f hf hc).val.fst (testLift g hg hgc).val.fst] with x h0 h1 h2 h3
  change _ = ((testLift f hf hc).val.fst - (testLift g hg hgc).val.fst) x
  rw [h0, h3, Pi.sub_apply, h1, h2]
  simp only [phiDoobInv, Pi.sub_apply, sub_div]

theorem testLift_phi (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    testLift (phiDoobTest v) (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc) =
      compactLift v hv hc := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [testLift_source (phiDoobTest v) _ _,
    (compact_memLp_mass hv.continuous hc).coeFn_toLp] with x h1 h2
  rw [h1, phiDoobInv_phiDoobTest]
  exact h2.symm

theorem sourcePair_translate (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) (hgc : HasCompactSupport g) (a : ℝ) :
    sourcePair (testLift (CHMDTranslation.translate f a) (CHMDTranslation.contDiff_translate hf a)
      (CHMDTranslation.compact_translate hc a))
      (testLift (CHMDTranslation.translate g a) (CHMDTranslation.contDiff_translate hg a)
        (CHMDTranslation.compact_translate hgc a)) = sourcePair (testLift f hf hc) (testLift g hg hgc) := by
  rw [sourcePair_polarization, sourcePair_polarization, ← testLift_add, ← testLift_add]
  simp only [testLift_energy]
  have he : CHMDTranslation.translate f a + CHMDTranslation.translate g a =
      CHMDTranslation.translate (f+g) a := rfl
  rw [he, CHMDTranslation.markovEnergy_translate, CHMDTranslation.markovEnergy_translate,
    CHMDTranslation.markovEnergy_translate]

/-- Signed difference energies plus source convergence suffice for graph completion. -/
theorem cauchySeq_of_energy_transfer (u v : ℕ → SourceGraph)
    (hv : CauchySeq v) (hs : CauchySeq (fun n => (u n).val.fst))
    (he : ∀ m n, sourceEnergy (u m-u n) = sourceEnergy (v m-v n)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff] at hv hs ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hv (ε/4) (by positivity)
  obtain ⟨K, hK⟩ := hs (ε/4) (by positivity)
  refine ⟨max N K, fun m hm n hn => ?_⟩
  have h1 := hN m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn)
  have h2 := hK m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)
  simp only [dist_eq_norm] at h1 h2 ⊢
  have hi := sourceEnergy_add_two_mass (u m-u n)
  rw [he m n] at hi
  have hj := sourceEnergy_add_two_mass (v m-v n)
  change sourceEnergy (v m-v n) + 2 * ‖(u m).val.fst-(u n).val.fst‖^2 = ‖u m-u n‖^2 at hi
  have ha : ‖v m-v n‖^2 < (ε/4)^2 := by nlinarith [norm_nonneg (v m-v n)]
  have hb : ‖(u m).val.fst-(u n).val.fst‖^2 < (ε/4)^2 := by
    nlinarith [norm_nonneg ((u m).val.fst-(u n).val.fst)]
  nlinarith [sq_nonneg ‖(v m-v n).val.fst‖, norm_nonneg (u m-u n)]

end RHTower.CHMDDoobGraph
