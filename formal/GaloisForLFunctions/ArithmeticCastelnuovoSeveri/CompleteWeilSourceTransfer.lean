import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellRealization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellLevyTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellMomentTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompletePrimeSourceTransfer
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeResonatorPositivity

/-!
# Complete logarithmic cells recover the Weil source form

One sequence of actual complete-cell sections retains the Gamma jump energy,
every prime translation, square mass, and both pole moments. Its arithmetic
quadratic forms converge to the original Weil form for every real compact C²
source. A common window also recovers polarized Gram entries.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open _root_.RHTower Zeta23

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open SpacingScaleHarmonicAnalysis

theorem memLp_logStep {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    MemLp (logStep f R N) 2 volume := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
  apply _root_.RHTower.CHMDDoobGraph.bounded_compact_memLp_volume
    (measurable_logStep hf.continuous.measurable R hN)
    (hasCompactSupport_logStep R hN hB hs) ((norm_nonneg (f 0)).trans (hC 0))
  intro u
  simpa only [Real.norm_eq_abs, logStep] using hC (logCellPoint R N u)

/-- The complete cells converge strongly in ordinary L² as well as in jump energy. -/
theorem tendsto_logStep_L2_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ∫ u, (logStep f R (N + 1) u - f u) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hf hc
  let window := Icc (-R) (Real.log B - R)
  have hlim : Tendsto (fun N : ℕ => ∫ u, (logStep f R (N + 1) u - f u) ^ 2)
      atTop (𝓝 (∫ _u : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (window.indicator (fun _ => (2 * C) ^ 2))
    · intro N
      exact (((measurable_logStep hf.continuous.measurable R (by omega)).sub
        hf.continuous.measurable).pow_const 2).aestronglyMeasurable
    · exact (integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const isCompact_Icc.measure_lt_top.ne)
    · intro N
      apply Eventually.of_forall
      intro u
      by_cases hu : u ∈ window
      · rw [indicator_of_mem hu, Real.norm_of_nonneg (sq_nonneg _)]
        have hb : |logStep f R (N + 1) u - f u| ≤ 2 * C := by
          have h : ‖f (logCellPoint R (N + 1) u) - f u‖ ≤ 2 * C :=
            (norm_sub_le _ _).trans
              (by linarith only [hC (logCellPoint R (N + 1) u), hC u])
          simpa only [Real.norm_eq_abs, logStep] using h
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
      · have hout : u ≤ -R ∨ Real.log B - R ≤ u := by
          dsimp only [window] at hu
          simp only [mem_Icc, not_and_or, not_le] at hu
          exact hu.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
        rw [logStep_eq_zero_outside R (by omega) hB hs hout, hs u hout,
          sub_self, zero_pow (by norm_num : 2 ≠ 0), norm_zero, indicator_of_notMem hu]
    · apply Eventually.of_forall
      intro u
      have ht := (tendsto_logStep hK R (fun x hx => hs x (Or.inl hx)) u).comp
        (tendsto_add_atTop_nat 1)
      have he : Tendsto (fun N : ℕ => logStep f R (N + 1) u - f u) atTop
          (𝓝 (f u - f u)) := ht.sub tendsto_const_nhds
      simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
        he.pow 2
  simpa only [integral_zero] using hlim

/-- A finite coefficient vector represented on translated logarithmic cells. -/
def finiteCellProfile (c : ℕ → ℝ) (R : ℝ) (N X : ℕ) (u : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc N X,
    (Ico (logEndpoint R N a) (logEndpoint R N (a + 1))).indicator (fun _ => c a) u

/-- The full arithmetic form depends only on the finite cell coefficients and coordinates. -/
def finiteCellWeil (c : ℕ → ℝ) (R : ℝ) (N X : ℕ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ u, finiteCellProfile c R N X u ^ 2) +
    levyEnergy (finiteCellProfile c R N X) - cellPrimeEnergy c N X +
      (2 * coshHalfMoment (finiteCellProfile c R N X) ^ 2 -
        2 * sinhHalfMoment (finiteCellProfile c R N X) ^ 2)

/-- The finite arithmetic cell form evaluated on logarithmic samples of a source. -/
def completeCellWeil (f : ℝ → ℝ) (R : ℝ) (N B : ℕ) : ℝ :=
  finiteCellWeil (logSamples f R N) R N (N * B)

theorem completeCellWeil_eq {f : ℝ → ℝ} (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    completeCellWeil f R N B =
      2 * gammaHardyPhaseRate 0 * (∫ u, logStep f R N u ^ 2) +
        levyEnergy (logStep f R N) - cellPrimeEnergy (logSamples f R N) N (N * B) +
          (2 * coshHalfMoment (logStep f R N) ^ 2 - 2 * sinhHalfMoment (logStep f R N) ^ 2) := by
  have hp : finiteCellProfile (logSamples f R N) R N (N * B) = logStep f R N := by
    funext u
    exact (logStep_eq_indicator_sum R hN hB hs u).symm
  simp only [completeCellWeil, finiteCellWeil, hp]

theorem tendsto_cellPrimeEnergy_on_window {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => cellPrimeEnergy (logSamples f R N) N (N * B)) atTop
      (𝓝 (primeSum f)) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hCa : ∀ u, |f u| ≤ C := fun u => by simpa only [Real.norm_eq_abs] using hC u
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hf hc
  obtain ⟨D, _hD, hd⟩ := exists_primeSpine_source_rate hf hf hc R hB
    (fun u hu => ⟨hs u hu, hs u hu⟩)
  let E := primeWeightSum B *
    (Real.sqrt ((B : ℝ) * C ^ 2) * Real.sqrt ((B : ℝ) ^ 2 * (K : ℝ) ^ 2))
  have hbound : ∀ N : ℕ, 1 ≤ N →
      |cellPrimeEnergy (logSamples f R N) N (N * B) - primeSum f| ≤ (E + D) / N := by
    intro N hN
    have hsupport := logSamples_eq_zero_above R hN hB
      (fun u hu => hs u (Or.inr hu.le))
    rw [← fullPrimeSectionPair_self_logSamples f R hN (N * B) (hs (-R) (Or.inl le_rfl)),
      ← smoothPrimePair_self_eq_primeSum,
      fullPrimeSectionPair_eq _ _ hN (N * B) hB le_rfl hsupport]
    have hsplit := abs_add_le
      (primeSectionPair (logSamples f R N) (logSamples f R N) N (N * B) B -
        primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B)
      (primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B - smoothPrimePair f f)
    rw [sub_add_sub_cancel, primeSectionPair_sub_spine _ _ hN (N * B) B hsupport] at hsplit
    calc
      _ ≤ |primeCellRemainder (logSamples f R N) (logSamples f R N) N (N * B) B| +
          |primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B -
            smoothPrimePair f f| := hsplit
      _ ≤ E / N + D / N := add_le_add
        (abs_primeCellRemainder_logSamples_le hC0 hCa hK R hN hB B
          (fun u hu => hs u (Or.inr hu.le))) (hd N hN)
      _ = _ := by ring
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    ?_ (tendsto_const_div_atTop_nhds_zero_nat (E + D))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact hbound N hN

/-- Every term of the original Weil source form is recovered on the same cells. -/
theorem tendsto_completeCellWeil {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => completeCellWeil f R (N + 1) B) atTop (𝓝 (weilQuad f)) := by
  have hm := tendsto_logStep_mass hf hc R hB hs
  have hl := tendsto_logStep_levyEnergy hf hc R hB hs
  have hp := (tendsto_cellPrimeEnergy_on_window hf hc R hB hs).comp (tendsto_add_atTop_nat 1)
  have hcosh := tendsto_logStep_coshHalfMoment hf hc R hB hs
  have hsinh := tendsto_logStep_sinhHalfMoment hf hc R hB hs
  have hlimit : Tendsto (fun N : ℕ =>
      2 * gammaHardyPhaseRate 0 * (∫ u, logStep f R (N + 1) u ^ 2) +
        levyEnergy (logStep f R (N + 1)) -
          cellPrimeEnergy (logSamples f R (N + 1)) (N + 1) ((N + 1) * B) +
            (2 * coshHalfMoment (logStep f R (N + 1)) ^ 2 -
              2 * sinhHalfMoment (logStep f R (N + 1)) ^ 2)) atTop (𝓝 (weilQuad f)) := by
    rw [weilQuad_eq hf hc]
    exact (((tendsto_const_nhds.mul hm).add hl).sub hp).add
      ((tendsto_const_nhds.mul (hcosh.pow 2)).sub (tendsto_const_nhds.mul (hsinh.pow 2)))
  exact Filter.Tendsto.congr' (Eventually.of_forall fun N =>
    (completeCellWeil_eq (f := f) R (N := N + 1) (by omega) hB hs).symm) hlimit

/-- Every real compact C² source has a complete-cell exhaustion recovering its Weil form. -/
theorem exists_completeWeilSource {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => completeCellWeil f R (N + 1) B) atTop (𝓝 (weilQuad f)) := by
  obtain ⟨R, hR, B, hB, _, _, hs, _⟩ := exists_compact_logSamples_rate hf hf hc hc
  exact ⟨R, hR, B, hB, tendsto_completeCellWeil hf hc R hB (fun u hu => (hs u hu).1)⟩

/-- The target form is the original zero-configuration intersection form. -/
theorem weilQuad_eq_zetaW {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    weilQuad f = (zetaZeroConfig.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re := by
  have hcomplex : ContDiff ℝ 2 (fun u => (f u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcompact : HasCompactSupport (fun u => (f u : ℂ)) := hc.comp_left Complex.ofReal_zero
  exact (congrArg Complex.re (zeta_W_eq_weilFullFunctional hcomplex hcompact)).symm

theorem exists_completeScalingSurfaceSource {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => completeCellWeil f R (N + 1) B) atTop
        (𝓝 ((zetaZeroConfig.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re)) := by
  simpa only [weilQuad_eq_zetaW hf hc] using exists_completeWeilSource hf hc

/-- Polarized entries of the complete cell form. -/
def completeCellGram (f g : ℝ → ℝ) (R : ℝ) (N B : ℕ) : ℝ :=
  (completeCellWeil (fun u => f u + g u) R N B -
    completeCellWeil (fun u => f u - g u) R N B) / 4

theorem tendsto_completeCellGram {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0 ∧ g u = 0) :
    Tendsto (fun N : ℕ => completeCellGram f g R (N + 1) B) atTop
      (𝓝 ((weilQuad (fun u => f u + g u) - weilQuad (fun u => f u - g u)) / 4)) := by
  have hplus : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u + g u = 0 := by
    intro u hu
    rw [(hs u hu).1, (hs u hu).2, add_zero]
  have hminus : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u - g u = 0 := by
    intro u hu
    rw [(hs u hu).1, (hs u hu).2, sub_self]
  exact ((tendsto_completeCellWeil (hf.add hg) (hfc.add hgc) R hB hplus).sub
    (tendsto_completeCellWeil (hf.sub hg) (hfc.sub hgc) R hB hminus)).div_const 4

/-- One common cell system recovers each polarized original Weil entry. -/
theorem exists_completeWeilGram {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => completeCellGram f g R (N + 1) B) atTop
        (𝓝 ((weilQuad (fun u => f u + g u) - weilQuad (fun u => f u - g u)) / 4)) := by
  obtain ⟨R, hR, B, hB, _, _, hs, _⟩ := exists_compact_logSamples_rate hf hg hfc hgc
  exact ⟨R, hR, B, hB, tendsto_completeCellGram hf hg hfc hgc R hB hs⟩

/-- Squared source magnitudes select a common window without cancellation. -/
theorem exists_common_logCell_window {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i)) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      ∀ i u, u ≤ -R ∨ Real.log B - R ≤ u → f i u = 0 := by
  classical
  let F := fun u => ∑ i, f i u ^ 2
  have hF : ContDiff ℝ 2 F := ContDiff.sum fun i _ => (hf i).pow 2
  have hFc : HasCompactSupport F :=
    _root_.RHTower.EvenSector.hasCompactSupport_finset_sum Finset.univ (fun i _ => by
      have he : (fun u => f i u ^ 2) = f i * f i := by
        funext u
        exact pow_two (f i u)
      rw [he]
      exact (hc i).mul_left)
  obtain ⟨R, hR, B, hB, _, _, hs, _⟩ := exists_compact_logSamples_rate hF hF hFc hFc
  refine ⟨R, hR, B, hB, fun i u hu => ?_⟩
  have hle : f i u ^ 2 ≤ F u :=
    Finset.single_le_sum (fun j _ => sq_nonneg (f j u)) (Finset.mem_univ i)
  rw [(hs u hu).1] at hle
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))

/-- A finite source space and all of its Gram entries use one complete-cell exhaustion. -/
theorem exists_completeFiniteSourceTransfer {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i)) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      (∀ c : ι → ℝ,
        Tendsto (fun N : ℕ => ∫ u,
          (logStep (fun x => ∑ i, c i * f i x) R (N + 1) u - ∑ i, c i * f i u) ^ 2)
          atTop (𝓝 0) ∧
        Tendsto (fun N : ℕ => completeCellWeil (fun u => ∑ i, c i * f i u) R (N + 1) B)
          atTop (𝓝 ((zetaZeroConfig.W
            (fun u => ((∑ i, c i * f i u : ℝ) : ℂ))
            (fun u => ((∑ i, c i * f i u : ℝ) : ℂ))).re))) ∧
      ∀ i j, Tendsto (fun N : ℕ => completeCellGram (f i) (f j) R (N + 1) B) atTop
        (𝓝 ((weilQuad (fun u => f i u + f j u) - weilQuad (fun u => f i u - f j u)) / 4)) := by
  classical
  obtain ⟨R, hR, B, hB, hs⟩ := exists_common_logCell_window f hf hc
  refine ⟨R, hR, B, hB, ?_, fun i j => ?_⟩
  · intro c
    have hcomb : ContDiff ℝ 2 (fun u => ∑ i, c i * f i u) :=
      ContDiff.sum fun i _ => contDiff_const.mul (hf i)
    have hcompact : HasCompactSupport (fun u => ∑ i, c i * f i u) :=
      _root_.RHTower.EvenSector.hasCompactSupport_finset_sum Finset.univ
        (fun i _ => (hc i).mul_left)
    have hsupport : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → ∑ i, c i * f i u = 0 := by
      intro u hu
      apply Finset.sum_eq_zero
      intro i _
      rw [hs i u hu, mul_zero]
    refine ⟨tendsto_logStep_L2_error hcomb hcompact R hB hsupport, ?_⟩
    rw [← weilQuad_eq_zetaW hcomb hcompact]
    exact tendsto_completeCellWeil hcomb hcompact R hB hsupport
  · exact tendsto_completeCellGram (hf i) (hf j) (hc i) (hc j) R hB
      (fun u hu => ⟨hs i u hu, hs j u hu⟩)

#print axioms exists_completeWeilSource
#print axioms memLp_logStep
#print axioms tendsto_logStep_L2_error
#print axioms exists_completeScalingSurfaceSource
#print axioms exists_completeWeilGram
#print axioms exists_completeFiniteSourceTransfer

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
