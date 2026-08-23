import GaloisForLFunctions.RHTower.XiWeilHardyFiberDeflatedQuartetBand

/-!
# Critical fixed-locus Poisson reserve in the exact quartet band

Critical-line conjugation partitions the Xi divisor into its fixed locus and free two-element
orbits.  The exact off-line-quartet height law makes every free-orbit resolvent pair
anti-Herglotz throughout an admissible central band.  The fixed locus contributes exactly its
positive upper-half-plane Poisson trace.

Thus the negative imaginary part of the continued prime--Gamma source dominates the entire
multiplicity-exact critical-line Poisson trace, not merely one selected Hardy fiber.  This is the
infinite fixed-locus form of the finite-fiber deletion law.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Multiplicity copies of Xi zeros on the critical line, expressed as the fixed-locus set of the
critical-line reflection. -/
def xiCriticalLineZeroCopySet : Set XiZeroCopy :=
  {q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2}

/-- Subtype of multiplicity copies in the critical fixed locus. -/
abbrev XiCriticalLineResolventCopy := xiCriticalLineZeroCopySet

/-- Relative-resolvent trace carried by the critical fixed locus. -/
def xiCriticalLineRelativeResolventTrace (z : ℂ) : ℂ :=
  ∑' q : XiCriticalLineResolventCopy, xiRelativeResolventTerm z q.1

/-- Relative-resolvent trace carried by free critical-line-reflection orbits. -/
def xiOffCriticalRelativeResolventTrace (z : ℂ) : ℂ :=
  ∑' q : ↥(xiCriticalLineZeroCopySetᶜ),
    xiRelativeResolventTerm z q.1

/-- Multiplicity-exact Poisson trace of the entire critical-line Xi divisor. -/
def xiCriticalLinePoissonTrace (z : ℂ) : ℝ :=
  ∑' q : XiCriticalLineResolventCopy,
    z.im / Complex.normSq (xiSpectralPoint q.1 - z)

/-- Critical copies are exactly fixed points of critical-line conjugation. -/
theorem mem_xiCriticalLineZeroCopySet_iff_lineConj_fixed (q : XiZeroCopy) :
    q ∈ xiCriticalLineZeroCopySet ↔ xiZeroCopyLineConjEquiv q = q := by
  rw [xiCriticalLineZeroCopySet, Set.mem_setOf_eq,
    xiZeroCopyLineConjEquiv_eq_self_iff_re_eq_half]

/-- A critical copy has a real centered spectral point. -/
theorem xiSpectralPoint_im_eq_zero_of_mem_criticalLine
    (q : XiCriticalLineResolventCopy) :
    (xiSpectralPoint q.1).im = 0 := by
  have hq : (q.1.1 : ℂ).re = 1 / 2 := q.2
  simp [xiSpectralPoint, Complex.mul_im, hq]

/-- One critical relative-resolvent atom is exactly minus its upper-half-plane Poisson kernel in
the imaginary coordinate. -/
theorem neg_im_xiRelativeResolventTerm_eq_poisson_of_criticalLine
    (z : ℂ) (q : XiCriticalLineResolventCopy) :
    -(xiRelativeResolventTerm z q.1).im =
      z.im / Complex.normSq (xiSpectralPoint q.1 - z) := by
  rw [xiRelativeResolventTerm, Complex.sub_im, Complex.inv_im, Complex.inv_im,
    xiSpectralPoint_im_eq_zero_of_mem_criticalLine q]
  simp only [neg_zero, zero_div, zero_sub, neg_neg]
  rw [Complex.sub_im, xiSpectralPoint_im_eq_zero_of_mem_criticalLine q]
  ring

/-- The critical-line Poisson trace converges at every point off the Xi divisor. -/
theorem summable_xiCriticalLinePoissonTerm {z : ℂ} (hXi : XiC z ≠ 0) :
    Summable (fun q : XiCriticalLineResolventCopy =>
      z.im / Complex.normSq (xiSpectralPoint q.1 - z)) := by
  have hsub : Summable (fun q : XiCriticalLineResolventCopy =>
      xiRelativeResolventTerm z q.1) :=
    (summable_xiRelativeResolventTerm hXi).subtype _
  have him : Summable (fun q : XiCriticalLineResolventCopy =>
      (xiRelativeResolventTerm z q.1).im) := by
    simpa only [Complex.imCLM_apply] using Complex.imCLM.summable hsub
  exact him.neg.congr fun q =>
    neg_im_xiRelativeResolventTerm_eq_poisson_of_criticalLine z q

/-- The critical fixed-locus trace has imaginary part equal to minus the complete critical-line
Poisson trace. -/
theorem neg_im_xiCriticalLineRelativeResolventTrace_eq_poisson
    {z : ℂ} (hXi : XiC z ≠ 0) :
    -(xiCriticalLineRelativeResolventTrace z).im =
      xiCriticalLinePoissonTrace z := by
  have hsub : Summable (fun q : XiCriticalLineResolventCopy =>
      xiRelativeResolventTerm z q.1) :=
    (summable_xiRelativeResolventTerm hXi).subtype _
  have himap := Complex.imCLM.map_tsum hsub
  change (∑' q : XiCriticalLineResolventCopy,
      xiRelativeResolventTerm z q.1).im =
    ∑' q : XiCriticalLineResolventCopy,
      (xiRelativeResolventTerm z q.1).im at himap
  rw [xiCriticalLineRelativeResolventTrace, xiCriticalLinePoissonTrace, himap]
  rw [← tsum_neg]
  exact tsum_congr fun q =>
    neg_im_xiRelativeResolventTerm_eq_poisson_of_criticalLine z q

/-- Off the Xi divisor, the full trace splits exactly into the critical fixed locus and the free
critical-line-reflection orbits. -/
theorem xiRelativeResolventTrace_eq_criticalLine_add_offCritical
    {z : ℂ} (hXi : XiC z ≠ 0) :
    xiRelativeResolventTrace z =
      xiCriticalLineRelativeResolventTrace z +
        xiOffCriticalRelativeResolventTrace z := by
  have hsum : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hXi
  have hsplit :=
    hsum.tsum_subtype_add_tsum_subtype_compl xiCriticalLineZeroCopySet
  simpa only [xiRelativeResolventTrace, xiCriticalLineRelativeResolventTrace,
    xiOffCriticalRelativeResolventTrace] using hsplit.symm

set_option maxHeartbeats 800000 in
/-- Every free reflection orbit remains anti-Herglotz throughout an exact off-line-quartet band. -/
theorem xiOffCriticalRelativeResolventTrace_im_nonpos_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiOffCriticalRelativeResolventTrace z).im ≤ 0 := by
  let C : Set XiZeroCopy := xiCriticalLineZeroCopySet
  let residual : XiZeroCopy → ℂ :=
    (Cᶜ).indicator (xiRelativeResolventTerm z)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand R hband z hzIm hzRe
  have hsum : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hXi
  have hresidual : Summable residual := hsum.indicator _
  have hfixed (q : XiZeroCopy) (hq : q ∈ C) :
      xiZeroCopyLineConjEquiv q = q := by
    exact (mem_xiCriticalLineZeroCopySet_iff_lineConj_fixed q).mp
      (by simpa only [C] using hq)
  have hmem (q : XiZeroCopy) :
      xiZeroCopyLineConjEquiv q ∈ C ↔ q ∈ C := by
    constructor
    · intro hq
      have hfix := hfixed (xiZeroCopyLineConjEquiv q) hq
      have hinvol :=
        DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply q
      have heq : xiZeroCopyLineConjEquiv q = q := by
        rw [hfix] at hinvol
        exact hinvol
      simpa only [heq] using hq
    · intro hq
      simpa only [hfixed q hq] using hq
  have hresidualJ : Summable
      (fun q : XiZeroCopy => residual (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hresidual
  have hpair := hresidual.add hresidualJ
  have hreindex :
      (∑' q : XiZeroCopy, residual (xiZeroCopyLineConjEquiv q)) =
        ∑' q : XiZeroCopy, residual q :=
    xiZeroCopyLineConjEquiv.tsum_eq residual
  have hpairsum :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q))) =
        2 * ∑' q : XiZeroCopy, residual q := by
    rw [hresidual.tsum_add hresidualJ, hreindex]
    ring
  have hpairsumIm := congrArg Complex.im hpairsum
  rw [Complex.im_tsum hpair] at hpairsumIm
  norm_num [mul_im] at hpairsumIm
  have hpairsumIm' :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q)).im) =
        2 * (∑' q : XiZeroCopy, residual q).im := by
    simpa only [Complex.add_im] using hpairsumIm
  have hpairsign :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q)).im) ≤ 0 := by
    refine tsum_nonpos fun q => ?_
    by_cases hq : q ∈ C
    · have hqJ : xiZeroCopyLineConjEquiv q ∈ C := (hmem q).2 hq
      simp [residual, hq, hqJ]
    · have hqJ : xiZeroCopyLineConjEquiv q ∉ C :=
        fun h => hq ((hmem q).1 h)
      simpa only [residual, Set.indicator, Set.mem_compl_iff,
        hq, hqJ, not_false_eq_true, ↓reduceIte] using
        xiRelativeResolventTerm_lineConj_pair_im_nonpos_offLineOrbit
          R hband z hzIm hzRe q
  have hoffEq :
      xiOffCriticalRelativeResolventTrace z =
        ∑' q : XiZeroCopy, residual q := by
    rw [xiOffCriticalRelativeResolventTrace]
    calc
      (∑' q : ↥(xiCriticalLineZeroCopySetᶜ),
          xiRelativeResolventTerm z q.1) =
          ∑' q : XiZeroCopy,
            (xiCriticalLineZeroCopySetᶜ).indicator
              (xiRelativeResolventTerm z) q :=
        tsum_subtype _ _
      _ = ∑' q : XiZeroCopy, residual q := by
        apply tsum_congr
        intro q
        simp only [residual, C]
  rw [hoffEq]
  linarith

/-- Full critical-line Poisson mass is an unconditional lower reserve for source dissipation on
every exact off-line-quartet band. -/
theorem xiCriticalLinePoissonTrace_le_neg_im_continuedPrimeArchSource_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    xiCriticalLinePoissonTrace z ≤
      -(continuedPrimeArchSourceRelativeTrace z).im := by
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzHalf
  have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzIm
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand R hband z hzIm hzRe
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  have hsplit := xiRelativeResolventTrace_eq_criticalLine_add_offCritical hXi
  have hoff :=
    xiOffCriticalRelativeResolventTrace_im_nonpos_exactOffLineQuartetBand
      R hband z hzIm hzRe
  have hcritical := neg_im_xiCriticalLineRelativeResolventTrace_eq_poisson hXi
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  have hsplitIm := congrArg Complex.im hsplit
  rw [Complex.add_im] at hsplitIm
  linarith

/-- Concrete all-critical-line Poisson reserve on `|Re z| ≤ 218 / 25`. -/
theorem xiCriticalLinePoissonTrace_le_neg_im_continuedPrimeArchSource_twoHundredEighteen_twentyFifths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 218 / 25) :
    xiCriticalLinePoissonTrace z ≤
      -(continuedPrimeArchSourceRelativeTrace z).im :=
  xiCriticalLinePoissonTrace_le_neg_im_continuedPrimeArchSource_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    z hzIm hzHalf hzRe

/-- Hardy's theorem supplies a multiplicity copy in the critical fixed locus. -/
theorem nonempty_xiCriticalLineResolventCopy_of_hardy :
    Nonempty XiCriticalLineResolventCopy := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support ρ
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
      omega
    exact ⟨ρ, ⟨0, hn⟩⟩
  refine ⟨⟨q, ?_⟩⟩
  change (q.1 : ℂ).re = 1 / 2
  simpa only [q] using hρ

/-- Hardy's unconditional critical-line zero makes the complete critical-locus Poisson reserve
strictly positive at every upper-half-plane point off the Xi divisor. -/
theorem xiCriticalLinePoissonTrace_pos
    {z : ℂ} (hzIm : 0 < z.im) (hXi : XiC z ≠ 0) :
    0 < xiCriticalLinePoissonTrace z := by
  classical
  let q : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  have hsum := summable_xiCriticalLinePoissonTerm hXi
  rw [xiCriticalLinePoissonTrace]
  refine hsum.tsum_pos (fun r => div_nonneg hzIm.le (Complex.normSq_nonneg _)) q ?_
  apply div_pos hzIm
  rw [Complex.normSq_pos]
  intro hzero
  have him := congrArg Complex.im hzero
  simp [xiSpectralPoint_im_eq_zero_of_mem_criticalLine q] at him
  linarith

/-- Concrete strict source sign on `|Re z| ≤ 218 / 25`. -/
theorem continuedPrimeArchSourceRelativeTrace_im_neg_twoHundredEighteen_twentyFifths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 218 / 25) :
    (continuedPrimeArchSourceRelativeTrace z).im < 0 :=
  continuedPrimeArchSourceRelativeTrace_im_neg_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    z hzIm hzHalf hzRe

/-- The complete critical-locus Poisson trace is nonnegative throughout the closed upper
half-plane. -/
theorem xiCriticalLinePoissonTrace_nonneg
    (z : ℂ) (hzIm : 0 ≤ z.im) :
    0 ≤ xiCriticalLinePoissonTrace z := by
  rw [xiCriticalLinePoissonTrace]
  exact tsum_nonneg fun q =>
    div_nonneg hzIm (Complex.normSq_nonneg _)

/-- Exact fixed/free conservation law for the continued source: after subtracting all critical
fixed-locus Poisson charge, the remaining dissipation is precisely the free-orbit dissipation. -/
theorem neg_im_continuedPrimeArchSource_sub_criticalLinePoissonTrace_eq_neg_im_offCritical
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    -(continuedPrimeArchSourceRelativeTrace z).im -
        xiCriticalLinePoissonTrace z =
      -(xiOffCriticalRelativeResolventTrace z).im := by
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzHalf
  have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzIm
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  have hsplit := xiRelativeResolventTrace_eq_criticalLine_add_offCritical hXi
  have hcritical := neg_im_xiCriticalLineRelativeResolventTrace_eq_poisson hXi
  have hsplitIm := congrArg Complex.im hsplit
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  rw [Complex.add_im] at hsplitIm
  linarith

/-- Under RH the free critical-line-reflection sector is empty, hence its relative-resolvent
trace vanishes identically. -/
theorem xiOffCriticalRelativeResolventTrace_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z : ℂ) :
    xiOffCriticalRelativeResolventTrace z = 0 := by
  letI : IsEmpty ↥(xiCriticalLineZeroCopySetᶜ) :=
    ⟨fun q => by
      have hfix := xiZeroCopyLineConjEquiv_eq_of_riemannHypothesis hRH q.1
      have hmem : q.1 ∈ xiCriticalLineZeroCopySet :=
        (mem_xiCriticalLineZeroCopySet_iff_lineConj_fixed q.1).2 hfix
      exact q.2 hmem⟩
  simp [xiOffCriticalRelativeResolventTrace]

/-- Under RH source dissipation is exactly, not merely bounded below by, the complete
critical-line Poisson trace. -/
theorem xiCriticalLinePoissonTrace_eq_neg_im_continuedPrimeArchSource_of_riemannHypothesis
    (hRH : RiemannHypothesis)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    xiCriticalLinePoissonTrace z =
      -(continuedPrimeArchSourceRelativeTrace z).im := by
  have hconservation :=
    neg_im_continuedPrimeArchSource_sub_criticalLinePoissonTrace_eq_neg_im_offCritical
      z hzIm hzHalf hzeta
  rw [xiOffCriticalRelativeResolventTrace_eq_zero_of_riemannHypothesis hRH z]
    at hconservation
  simp only [zero_im, neg_zero] at hconservation
  linarith

/-- Global source margin paying the entire critical fixed-locus Poisson trace. -/
def CriticalLocusPrimeGammaPoissonMargin : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      xiCriticalLinePoissonTrace z ≤
        -(continuedPrimeArchSourceRelativeTrace z).im

/-- RH is exactly the statement that source dissipation pays the complete critical fixed-locus
Poisson charge.  Under RH this margin is an equality. -/
theorem riemannHypothesis_iff_criticalLocusPrimeGammaPoissonMargin :
    RiemannHypothesis ↔ CriticalLocusPrimeGammaPoissonMargin := by
  constructor
  · intro hRH z hzIm hzHalf hzeta
    exact le_of_eq
      (xiCriticalLinePoissonTrace_eq_neg_im_continuedPrimeArchSource_of_riemannHypothesis
        hRH z hzIm hzHalf hzeta)
  · intro hmargin
    apply continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mp
    intro z hzIm hzHalf hzeta
    have hpay := hmargin z hzIm hzHalf hzeta
    have hnonneg := xiCriticalLinePoissonTrace_nonneg z hzIm.le
    linarith

/-- Passivity of the free reflection-orbit sector after removing the critical fixed locus. -/
def OffCriticalRelativeResolventUpperAntiHerglotz : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (xiOffCriticalRelativeResolventTrace z).im ≤ 0

/-- Fixed/free sector form of the RH endpoint: RH is equivalent to passivity of only the free
reflection-orbit resolvent sector. -/
theorem riemannHypothesis_iff_offCriticalRelativeResolventUpperAntiHerglotz :
    RiemannHypothesis ↔ OffCriticalRelativeResolventUpperAntiHerglotz := by
  constructor
  · intro hRH z _hzIm _hzHalf _hzeta
    rw [xiOffCriticalRelativeResolventTrace_eq_zero_of_riemannHypothesis hRH z]
    exact le_rfl
  · intro hfree
    apply continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mp
    intro z hzIm hzHalf hzeta
    have hconservation :=
      neg_im_continuedPrimeArchSource_sub_criticalLinePoissonTrace_eq_neg_im_offCritical
        z hzIm hzHalf hzeta
    have hfreeZ := hfree z hzIm hzHalf hzeta
    have hnonneg := xiCriticalLinePoissonTrace_nonneg z hzIm.le
    linarith

end

end RHTower
