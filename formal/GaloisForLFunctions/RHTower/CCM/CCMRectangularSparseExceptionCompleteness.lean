import GaloisForLFunctions.RHTower.CCM.CCMRectangularNegativePartEnergyGate

/-!
# Exact exceptional-carrier completeness for one fixed rectangular Weil window

For every exceptional aperture set, RH is equivalent to finite Dirichlet energy of the actual
negative Weil mass carried by that set together with one-sided subpower lower control on its
complement.  This exponent-free theorem is exact: under false RH every exceptional carrier must
expose failure in one of those two channels.

The fixed-window observable also has an unconditional square-root bound.  Consequently the exact
energy law admits explicit outer envelopes: a budget-matched power law, a self-calibrating law at
the sharp transverse exponent, and a divisor-independent half-power law.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- Universal coefficient in the unconditional square-root bound. -/
def xiRectangularWeilHalfPowerBound (L : ℝ) : ℝ :=
  2 * xiRectangularRightCoefficientNormSum L +
    rectangularTwoEdgeRemainderBound L *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2

theorem xiRectangularWeilHalfPowerBound_nonneg (L : ℝ) :
    0 ≤ xiRectangularWeilHalfPowerBound L := by
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (tsum_nonneg fun q => norm_nonneg _)
  · exact mul_nonneg (by unfold rectangularTwoEdgeRemainderBound; positivity)
      (tsum_nonneg fun q => by positivity)

/-- Every admissible fixed-window observable has the universal square-root growth bound. -/
theorem norm_xiRectangularWeilLogCoefficient_le_halfPower
    {L : ℝ} {N n : ℕ}
    (hN : ∀ m : ℕ, N ≤ m → 1 ≤ m ∧ L ≤ Real.log m / 2)
    (hnN : N ≤ n) :
    ‖xiRectangularWeilLogCoefficient L n‖ ≤
      xiRectangularWeilHalfPowerBound L * (n : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨hn1, hLa⟩ := hN n hnN
  have hcarrier := norm_xiRectangularRightDirichletComplex_le L
    (δ := (1 / 2 : ℝ))
    (fun q => le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2) hn1
  have hrem := norm_xiRectangularWeilRemainderCoefficient_le hN n
  have hpref : xiRectangularLandauPrefixCoefficient L 0 N n = 0 := by
    rw [xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hnN)]
  have htail : xiRectangularWeilTailCoefficient L N n =
      xiRectangularWeilLogCoefficient L n := by
    rw [xiRectangularWeilTailCoefficient, if_pos hnN]
  have heq := xiRectangularWeilTailCoefficient_eq_carrier_sub_prefix_add_remainder L N n
  rw [htail, hpref, sub_zero] at heq
  have htri : ‖xiRectangularWeilLogCoefficient L n‖ ≤
      ‖xiRectangularRightDirichletComplex L n‖ +
        ‖xiRectangularWeilRemainderCoefficient L N n‖ := by
    rw [heq]
    exact norm_add_le _ _
  have hpow : 1 ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
  have hK : 0 ≤ rectangularTwoEdgeRemainderBound L *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
    mul_nonneg (by unfold rectangularTwoEdgeRemainderBound; positivity)
      (tsum_nonneg fun q => by positivity)
  calc
    ‖xiRectangularWeilLogCoefficient L n‖ ≤
        ‖xiRectangularRightDirichletComplex L n‖ +
          ‖xiRectangularWeilRemainderCoefficient L N n‖ := htri
    _ ≤ 2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ (1 / 2 : ℝ) +
          rectangularTwoEdgeRemainderBound L *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by gcongr
    _ ≤ 2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ (1 / 2 : ℝ) +
          (rectangularTwoEdgeRemainderBound L *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
              (n : ℝ) ^ (1 / 2 : ℝ) := by
        exact add_le_add_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hK) _
    _ = xiRectangularWeilHalfPowerBound L * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [xiRectangularWeilHalfPowerBound]
      ring

/-- The universal square-root exceptional majorant supported on `E`. -/
def xiRectangularHalfPowerExceptionalCoefficient (E : Set ℕ) (n : ℕ) : ℝ :=
  E.indicator (fun m => powerCorrectionCoefficient (1 / 2 : ℝ) m) n

theorem xiRectangularHalfPowerExceptionalCoefficient_nonneg
    (E : Set ℕ) (n : ℕ) :
    0 ≤ xiRectangularHalfPowerExceptionalCoefficient E n := by
  by_cases hn : n ∈ E
  · rw [xiRectangularHalfPowerExceptionalCoefficient, Set.indicator_of_mem hn]
    exact powerCorrectionCoefficient_nonneg _ _
  · rw [xiRectangularHalfPowerExceptionalCoefficient, Set.indicator_of_notMem hn]

/-- An exceptional aperture set is half-power thin when its square-root majorant has
Dirichlet energy on every line strictly to the right of one. -/
def XiRectangularHalfPowerExceptionalEnergy (E : Set ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((xiRectangularHalfPowerExceptionalCoefficient E n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

/-- One-sided subpower control away from an exceptional aperture set. -/
def XiRectangularWeilSubpowerLowerOff
    (L : ℝ) (N : ℕ) (E : Set ℕ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n → n ∉ E →
      0 ≤ (xiRectangularWeilLogCoefficient L n).re +
        C * powerCorrectionCoefficient delta n

/-! ## Exact exceptional-carrier decomposition -/

/-- The actual negative Weil mass carried by an exceptional aperture set.  Unlike the power
majorants below, this charges only the negative part which can obstruct positivity. -/
def xiRectangularExceptionalNegativeCoefficient
    (L : ℝ) (N : ℕ) (E : Set ℕ) (n : ℕ) : ℝ :=
  E.indicator (fun m => xiRectangularWeilTailNegativePart L N m) n

theorem xiRectangularExceptionalNegativeCoefficient_nonneg
    (L : ℝ) (N : ℕ) (E : Set ℕ) (n : ℕ) :
    0 ≤ xiRectangularExceptionalNegativeCoefficient L N E n := by
  by_cases hn : n ∈ E
  · rw [xiRectangularExceptionalNegativeCoefficient, Set.indicator_of_mem hn]
    exact xiRectangularWeilTailNegativePart_nonneg L N n
  · rw [xiRectangularExceptionalNegativeCoefficient, Set.indicator_of_notMem hn]

/-- Exact Dirichlet-energy cost of the negative Weil mass carried by `E`. -/
def XiRectangularExceptionalNegativeEnergy
    (L : ℝ) (N : ℕ) (E : Set ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((xiRectangularExceptionalNegativeCoefficient L N E n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

private def xiRectangularExceptionalCarrierMajorant
    (L : ℝ) (N : ℕ) (E : Set ℕ) (C delta : ℝ) (n : ℕ) : ℝ :=
  C * powerCorrectionCoefficient delta n +
    xiRectangularExceptionalNegativeCoefficient L N E n

private theorem xiRectangularExceptionalCarrierMajorant_nonneg
    (L : ℝ) (N : ℕ) (E : Set ℕ)
    {C delta : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ xiRectangularExceptionalCarrierMajorant L N E C delta n := by
  exact add_nonneg
    (mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _))
    (xiRectangularExceptionalNegativeCoefficient_nonneg L N E n)

private theorem xiRectangularExceptionalCarrierMajorant_LSeriesSummable
    (L : ℝ) (N : ℕ) (E : Set ℕ)
    (hE : XiRectangularExceptionalNegativeEnergy L N E)
    {epsilon C delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 1 + delta < 1 + epsilon) :
    LSeriesSummable
      (fun n => ((xiRectangularExceptionalCarrierMajorant
        L N E C delta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hpower := powerCorrectionCoefficient_LSeriesSummable
    (alpha := delta) (s := (((1 + epsilon : ℝ) : ℂ))) (by
      simpa only [ofReal_re] using hdelta)
  have hexc := hE epsilon hepsilon
  have hadd := (hpower.smul (C : ℂ)).add hexc
  change Summable (LSeries.term
    (fun n => ((xiRectangularExceptionalCarrierMajorant
      L N E C delta n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      xiRectangularExceptionalCarrierMajorant, ofReal_add, ofReal_mul]

private theorem xiRectangularWeilTailNegativePart_le_exceptionalCarrierMajorant
    {L : ℝ} {N : ℕ} (E : Set ℕ)
    {C delta : ℝ} (hC : 0 ≤ C)
    (hlower : ∀ n : ℕ, N ≤ n → n ∉ E →
      0 ≤ (xiRectangularWeilLogCoefficient L n).re +
        C * powerCorrectionCoefficient delta n) :
    ∀ n : ℕ, xiRectangularWeilTailNegativePart L N n ≤
      xiRectangularExceptionalCarrierMajorant L N E C delta n := by
  intro n
  by_cases hnE : n ∈ E
  · rw [xiRectangularExceptionalCarrierMajorant,
      xiRectangularExceptionalNegativeCoefficient, Set.indicator_of_mem hnE]
    exact le_add_of_nonneg_left
      (mul_nonneg hC (powerCorrectionCoefficient_nonneg delta n))
  · rw [xiRectangularExceptionalCarrierMajorant,
      xiRectangularExceptionalNegativeCoefficient, Set.indicator_of_notMem hnE,
      add_zero]
    by_cases hnN : N ≤ n
    · rw [xiRectangularWeilTailNegativePart,
        xiRectangularWeilTailCoefficient, if_pos hnN]
      have hgood := hlower n hnN hnE
      have hpow : 0 ≤ C * powerCorrectionCoefficient delta n :=
        mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)
      change max (-(xiRectangularWeilLogCoefficient L n).re) 0 ≤ _
      exact max_le (by linarith) hpow
    · rw [xiRectangularWeilTailNegativePart,
        xiRectangularWeilTailCoefficient, if_neg hnN, Complex.zero_re,
        negPart_zero]
      exact mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)

/-- Under RH the negative part of every fixed-window tail vanishes identically. -/
theorem xiRectangularWeilTailNegativePart_eq_zero_of_riemannHypothesis
    {L : ℝ} (hL : 0 < L) (hRH : RiemannHypothesis) (N n : ℕ) :
    xiRectangularWeilTailNegativePart L N n = 0 := by
  by_cases hnN : N ≤ n
  · rw [xiRectangularWeilTailNegativePart,
      xiRectangularWeilTailCoefficient, if_pos hnN, negPart_eq_zero]
    have hpos :=
      (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
    simpa [xiRectangularWeilLogCoefficient] using hpos
  · rw [xiRectangularWeilTailNegativePart,
      xiRectangularWeilTailCoefficient, if_neg hnN, Complex.zero_re,
      negPart_zero]

/-- **Exact exceptional-carrier decomposition.** For every partition of logarithmic apertures
into `E` and its complement, RH is equivalent to finite negative Dirichlet energy on `E`
together with one-sided subpower lower control off `E`. -/
theorem riemannHypothesis_iff_exceptionalNegativeEnergy_and_subpowerLowerOff
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) :
    RiemannHypothesis ↔
      XiRectangularExceptionalNegativeEnergy L N E ∧
        XiRectangularWeilSubpowerLowerOff L N E := by
  constructor
  · intro hRH
    constructor
    · intro epsilon hepsilon
      have hzero :
          (fun n => ((xiRectangularExceptionalNegativeCoefficient
            L N E n : ℝ) : ℂ)) = 0 := by
        funext n
        by_cases hnE : n ∈ E
        · rw [xiRectangularExceptionalNegativeCoefficient,
            Set.indicator_of_mem hnE,
            xiRectangularWeilTailNegativePart_eq_zero_of_riemannHypothesis
              hL hRH]
          rfl
        · rw [xiRectangularExceptionalNegativeCoefficient,
            Set.indicator_of_notMem hnE]
          rfl
      rw [hzero]
      exact LSeriesSummable_zero
    · intro delta hdelta
      refine ⟨0, le_rfl, fun n hnN hnE => ?_⟩
      have hpos :=
        (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
      simpa [xiRectangularWeilLogCoefficient] using hpos
  · rintro ⟨hE, hlower⟩
    apply riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy hL hN
    intro epsilon hepsilon
    let delta := epsilon / 2
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    obtain ⟨C, hC, hlowerC⟩ := hlower delta hdelta
    apply LSeriesSummable_of_nonneg_of_le
      (xiRectangularWeilTailNegativePart_nonneg L N)
      (xiRectangularExceptionalCarrierMajorant_nonneg L N E hC)
      (xiRectangularWeilTailNegativePart_le_exceptionalCarrierMajorant
        E hC hlowerC)
    apply xiRectangularExceptionalCarrierMajorant_LSeriesSummable
      L N E hE hepsilon
    dsimp [delta]
    linarith

/-- **Universal carrier dichotomy under false RH.** Every exceptional carrier must expose the
failure in one of exactly two channels: either its complement has non-subpower negative
excursions, or the negative mass it carries has divergent Dirichlet energy on some line to the
right of one. -/
theorem exceptionalCarrierDichotomy_of_not_riemannHypothesis
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) (E : Set ℕ) :
    ¬ XiRectangularWeilSubpowerLowerOff L N E ∨
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ¬ LSeriesSummable
          (fun n => ((xiRectangularExceptionalNegativeCoefficient
            L N E n : ℝ) : ℂ))
          (((1 + epsilon : ℝ) : ℂ)) := by
  by_cases hlower : XiRectangularWeilSubpowerLowerOff L N E
  · right
    by_contra hdiv
    push Not at hdiv
    have hE : XiRectangularExceptionalNegativeEnergy L N E := by
      intro epsilon hepsilon
      exact hdiv epsilon hepsilon
    exact hnot
      ((riemannHypothesis_iff_exceptionalNegativeEnergy_and_subpowerLowerOff
        hL hN E).mpr ⟨hE, hlower⟩)
  · exact Or.inl hlower

private def xiRectangularSparseNegativeMajorant
    (L : ℝ) (E : Set ℕ) (C delta : ℝ) (n : ℕ) : ℝ :=
  C * powerCorrectionCoefficient delta n +
    xiRectangularWeilHalfPowerBound L *
      xiRectangularHalfPowerExceptionalCoefficient E n

private theorem xiRectangularSparseNegativeMajorant_nonneg
    (L : ℝ) (E : Set ℕ) {C delta : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ xiRectangularSparseNegativeMajorant L E C delta n := by
  apply add_nonneg
  · exact mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)
  · exact mul_nonneg (xiRectangularWeilHalfPowerBound_nonneg L)
      (xiRectangularHalfPowerExceptionalCoefficient_nonneg E n)

private theorem xiRectangularSparseNegativeMajorant_LSeriesSummable
    (L : ℝ) (E : Set ℕ)
    (hE : XiRectangularHalfPowerExceptionalEnergy E)
    {epsilon C delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 1 + delta < 1 + epsilon) :
    LSeriesSummable
      (fun n => ((xiRectangularSparseNegativeMajorant L E C delta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hpower := powerCorrectionCoefficient_LSeriesSummable
    (alpha := delta) (s := (((1 + epsilon : ℝ) : ℂ))) (by
      simpa only [ofReal_re] using hdelta)
  have hexc := hE epsilon hepsilon
  have hadd := (hpower.smul (C : ℂ)).add
    (hexc.smul (xiRectangularWeilHalfPowerBound L : ℂ))
  change Summable (LSeries.term
    (fun n => ((xiRectangularSparseNegativeMajorant L E C delta n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      xiRectangularSparseNegativeMajorant, ofReal_add, ofReal_mul]

private theorem xiRectangularWeilTailNegativePart_le_sparseMajorant
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) {C delta : ℝ} (hC : 0 ≤ C)
    (hlower : ∀ n : ℕ, N ≤ n → n ∉ E →
      0 ≤ (xiRectangularWeilLogCoefficient L n).re +
        C * powerCorrectionCoefficient delta n) :
    ∀ n : ℕ, xiRectangularWeilTailNegativePart L N n ≤
      xiRectangularSparseNegativeMajorant L E C delta n := by
  intro n
  by_cases hnN : N ≤ n
  · rw [xiRectangularWeilTailNegativePart,
      xiRectangularWeilTailCoefficient, if_pos hnN]
    by_cases hnE : n ∈ E
    · have hnorm := norm_xiRectangularWeilLogCoefficient_le_halfPower hN hnN
      have hn0 : n ≠ 0 := by
        have hn1 := (hN n hnN).1
        omega
      have hnegabs : ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
          |(xiRectangularWeilLogCoefficient L n).re| := by
        change max (-(xiRectangularWeilLogCoefficient L n).re) 0 ≤
          |(xiRectangularWeilLogCoefficient L n).re|
        exact max_le (neg_le_abs _) (abs_nonneg _)
      have hneg : ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
          xiRectangularWeilHalfPowerBound L * (n : ℝ) ^ (1 / 2 : ℝ) :=
        hnegabs.trans ((Complex.abs_re_le_norm _).trans hnorm)
      have hhalf : powerCorrectionCoefficient (1 / 2 : ℝ) n =
          (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [powerCorrectionCoefficient, if_neg hn0]
      rw [xiRectangularSparseNegativeMajorant,
        xiRectangularHalfPowerExceptionalCoefficient, Set.indicator_of_mem hnE, hhalf]
      exact hneg.trans (le_add_of_nonneg_left
        (mul_nonneg hC (powerCorrectionCoefficient_nonneg delta n)))
    · have hgood := hlower n hnN hnE
      have hpow : 0 ≤ C * powerCorrectionCoefficient delta n :=
        mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)
      have hneg : ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
          C * powerCorrectionCoefficient delta n := by
        change max (-(xiRectangularWeilLogCoefficient L n).re) 0 ≤ _
        apply max_le
        · linarith
        · exact hpow
      rw [xiRectangularSparseNegativeMajorant,
        xiRectangularHalfPowerExceptionalCoefficient, Set.indicator_of_notMem hnE,
        mul_zero, add_zero]
      exact hneg
  · rw [xiRectangularWeilTailNegativePart,
      xiRectangularWeilTailCoefficient, if_neg hnN, Complex.zero_re,
      negPart_zero]
    exact xiRectangularSparseNegativeMajorant_nonneg L E hC n

/-- **Sparse-exception fixed-window completeness.** One-sided subpower control may fail on a
half-power-thin set of logarithmic integer apertures and still force RH. -/
theorem riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hE : XiRectangularHalfPowerExceptionalEnergy E)
    (hlower : XiRectangularWeilSubpowerLowerOff L N E) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy hL hN
  intro epsilon hepsilon
  let delta := epsilon / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  obtain ⟨C, hC, hlowerC⟩ := hlower delta hdelta
  apply LSeriesSummable_of_nonneg_of_le
    (xiRectangularWeilTailNegativePart_nonneg L N)
    (xiRectangularSparseNegativeMajorant_nonneg L E hC)
    (xiRectangularWeilTailNegativePart_le_sparseMajorant hN E hC hlowerC)
  apply xiRectangularSparseNegativeMajorant_LSeriesSummable L E hE hepsilon
  dsimp [delta]
  linarith

/-- For every fixed half-power-thin exceptional set, sparse-exception subpower control is exactly
equivalent to RH. -/
theorem riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hE : XiRectangularHalfPowerExceptionalEnergy E) :
    RiemannHypothesis ↔ XiRectangularWeilSubpowerLowerOff L N E := by
  constructor
  · intro hRH delta hdelta
    refine ⟨0, le_rfl, fun n hnN hnE => ?_⟩
    have hpos :=
      (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
    simpa [xiRectangularWeilLogCoefficient] using hpos
  · exact riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff hL hN E hE

/-- Positivity is allowed to fail on any half-power-thin exceptional aperture set. -/
theorem riemannHypothesis_of_xiRectangularWeil_nonnegative_off
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hE : XiRectangularHalfPowerExceptionalEnergy E)
    (hpos : ∀ n : ℕ, N ≤ n → n ∉ E →
      0 ≤ (xiRectangularWeilLogCoefficient L n).re) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff hL hN E hE
  intro delta hdelta
  exact ⟨0, le_rfl, fun n hnN hnE => by simpa using hpos n hnN hnE⟩

/-- **Positive thickness law under false RH.** If all non-subpower negative excursions are
confined to `E`, then false RH forces the square-root exceptional Dirichlet energy to diverge on
at least one line to the right of one. -/
theorem exists_halfPowerExceptionalEnergy_divergence_of_not_riemannHypothesis
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hlower : XiRectangularWeilSubpowerLowerOff L N E)
    (hnot : ¬ RiemannHypothesis) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ¬ LSeriesSummable
        (fun n => ((xiRectangularHalfPowerExceptionalCoefficient E n : ℝ) : ℂ))
        (((1 + epsilon : ℝ) : ℂ)) := by
  by_contra hdiv
  push Not at hdiv
  have hE : XiRectangularHalfPowerExceptionalEnergy E := by
    intro epsilon hepsilon
    exact hdiv epsilon hepsilon
  exact hnot
    (riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff hL hN E hE hlower)

/-! ## Self-calibrating transverse-exponent form -/

/-- The exceptional majorant calibrated to an arbitrary global power exponent. -/
def xiRectangularPowerExceptionalCoefficient
    (beta : ℝ) (E : Set ℕ) (n : ℕ) : ℝ :=
  E.indicator (fun m => powerCorrectionCoefficient beta m) n

theorem xiRectangularPowerExceptionalCoefficient_nonneg
    (beta : ℝ) (E : Set ℕ) (n : ℕ) :
    0 ≤ xiRectangularPowerExceptionalCoefficient beta E n := by
  by_cases hn : n ∈ E
  · rw [xiRectangularPowerExceptionalCoefficient, Set.indicator_of_mem hn]
    exact powerCorrectionCoefficient_nonneg _ _
  · rw [xiRectangularPowerExceptionalCoefficient, Set.indicator_of_notMem hn]

/-- An exceptional set is `beta`-thin when its `n^beta` majorant has Dirichlet energy on every
line strictly to the right of one. -/
def XiRectangularPowerExceptionalEnergy (beta : ℝ) (E : Set ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((xiRectangularPowerExceptionalCoefficient beta E n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

private def xiRectangularPowerSparseNegativeMajorant
    (beta B : ℝ) (E : Set ℕ) (C delta : ℝ) (n : ℕ) : ℝ :=
  C * powerCorrectionCoefficient delta n +
    B * xiRectangularPowerExceptionalCoefficient beta E n

private theorem xiRectangularPowerSparseNegativeMajorant_nonneg
    (beta : ℝ) {B : ℝ} (hB : 0 ≤ B) (E : Set ℕ)
    {C delta : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ xiRectangularPowerSparseNegativeMajorant beta B E C delta n := by
  apply add_nonneg
  · exact mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)
  · exact mul_nonneg hB
      (xiRectangularPowerExceptionalCoefficient_nonneg beta E n)

private theorem xiRectangularPowerSparseNegativeMajorant_LSeriesSummable
    (beta B : ℝ) (E : Set ℕ)
    (hE : XiRectangularPowerExceptionalEnergy beta E)
    {epsilon C delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 1 + delta < 1 + epsilon) :
    LSeriesSummable
      (fun n => ((xiRectangularPowerSparseNegativeMajorant
        beta B E C delta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hpower := powerCorrectionCoefficient_LSeriesSummable
    (alpha := delta) (s := (((1 + epsilon : ℝ) : ℂ))) (by
      simpa only [ofReal_re] using hdelta)
  have hexc := hE epsilon hepsilon
  have hadd := (hpower.smul (C : ℂ)).add (hexc.smul (B : ℂ))
  change Summable (LSeries.term
    (fun n => ((xiRectangularPowerSparseNegativeMajorant
      beta B E C delta n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      xiRectangularPowerSparseNegativeMajorant, ofReal_add, ofReal_mul]

private theorem xiRectangularWeilTailNegativePart_le_powerSparseMajorant
    {L : ℝ} {N : ℕ}
    {beta B : ℝ} (hB : 0 ≤ B) (E : Set ℕ)
    (hglobal : ∀ n : ℕ, N ≤ n →
      ‖xiRectangularWeilLogCoefficient L n‖ ≤
        B * powerCorrectionCoefficient beta n)
    {C delta : ℝ} (hC : 0 ≤ C)
    (hlower : ∀ n : ℕ, N ≤ n → n ∉ E →
      0 ≤ (xiRectangularWeilLogCoefficient L n).re +
        C * powerCorrectionCoefficient delta n) :
    ∀ n : ℕ, xiRectangularWeilTailNegativePart L N n ≤
      xiRectangularPowerSparseNegativeMajorant beta B E C delta n := by
  intro n
  by_cases hnN : N ≤ n
  · rw [xiRectangularWeilTailNegativePart,
      xiRectangularWeilTailCoefficient, if_pos hnN]
    by_cases hnE : n ∈ E
    · have hnorm := hglobal n hnN
      have hnegabs : ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
          |(xiRectangularWeilLogCoefficient L n).re| := by
        change max (-(xiRectangularWeilLogCoefficient L n).re) 0 ≤
          |(xiRectangularWeilLogCoefficient L n).re|
        exact max_le (neg_le_abs _) (abs_nonneg _)
      have hneg : ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
          B * powerCorrectionCoefficient beta n :=
        hnegabs.trans ((Complex.abs_re_le_norm _).trans hnorm)
      rw [xiRectangularPowerSparseNegativeMajorant,
        xiRectangularPowerExceptionalCoefficient, Set.indicator_of_mem hnE]
      exact hneg.trans (le_add_of_nonneg_left
        (mul_nonneg hC (powerCorrectionCoefficient_nonneg delta n)))
    · have hgood := hlower n hnN hnE
      have hpow : 0 ≤ C * powerCorrectionCoefficient delta n :=
        mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)
      have hneg : ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
          C * powerCorrectionCoefficient delta n := by
        change max (-(xiRectangularWeilLogCoefficient L n).re) 0 ≤ _
        apply max_le
        · linarith
        · exact hpow
      rw [xiRectangularPowerSparseNegativeMajorant,
        xiRectangularPowerExceptionalCoefficient, Set.indicator_of_notMem hnE,
        mul_zero, add_zero]
      exact hneg
  · rw [xiRectangularWeilTailNegativePart,
      xiRectangularWeilTailCoefficient, if_neg hnN, Complex.zero_re,
      negPart_zero]
    exact xiRectangularPowerSparseNegativeMajorant_nonneg beta hB E hC n

/-- **Budget-matched sparse-exception completeness.** If the complete fixed-window observable has
global power cost `n^beta`, then one-sided subpower control may fail on any exceptional set whose
`n^beta` majorant has finite Dirichlet energy on every line to the right of one. -/
theorem riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff_of_powerEnergy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {beta B : ℝ} (hB : 0 ≤ B) (E : Set ℕ)
    (hE : XiRectangularPowerExceptionalEnergy beta E)
    (hglobal : ∀ n : ℕ, N ≤ n →
      ‖xiRectangularWeilLogCoefficient L n‖ ≤
        B * powerCorrectionCoefficient beta n)
    (hlower : XiRectangularWeilSubpowerLowerOff L N E) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy hL hN
  intro epsilon hepsilon
  let delta := epsilon / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  obtain ⟨C, hC, hlowerC⟩ := hlower delta hdelta
  apply LSeriesSummable_of_nonneg_of_le
    (xiRectangularWeilTailNegativePart_nonneg L N)
    (xiRectangularPowerSparseNegativeMajorant_nonneg beta hB E hC)
    (xiRectangularWeilTailNegativePart_le_powerSparseMajorant
      hB E hglobal hC hlowerC)
  apply xiRectangularPowerSparseNegativeMajorant_LSeriesSummable
    beta B E hE hepsilon
  dsimp [delta]
  linarith

/-- The self-calibrating exceptional class uses the exact transverse exponent of the observable
itself, not the universal square-root envelope. -/
def XiRectangularTransverseExceptionalEnergy (E : Set ℕ) : Prop :=
  XiRectangularPowerExceptionalEnergy xiRightTransverseSup E

/-- **Self-calibrating sparse-exception completeness.** The exceptional cost is exactly the
sharp transverse exponent `xiRightTransverseSup`; the universal half-power theorem is its
divisor-independent corollary. -/
theorem riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff_transverse
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hE : XiRectangularTransverseExceptionalEnergy E)
    (hlower : XiRectangularWeilSubpowerLowerOff L N E) :
    RiemannHypothesis := by
  by_contra hnot
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
  apply hnot
  apply riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff_of_powerEnergy
    hL hN (xiRectangularWeilHalfPowerBound_nonneg L) E hE
  · intro n hnN
    obtain ⟨hn1, hLa⟩ := hN n hnN
    have hbound :=
      norm_xiWeilPolarization_rectangular_logSample_le_transverse_power
        (L := L) hne hn1 hLa
    have hn0 : n ≠ 0 := by omega
    simpa [xiRectangularWeilLogCoefficient,
      xiRectangularWeilHalfPowerBound, powerCorrectionCoefficient, hn0] using hbound
  · exact hlower

/-- For each fixed transverse-thin exceptional set, off-exception subpower lower control is
exactly equivalent to RH. -/
theorem riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff_transverse
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hE : XiRectangularTransverseExceptionalEnergy E) :
    RiemannHypothesis ↔ XiRectangularWeilSubpowerLowerOff L N E := by
  constructor
  · intro hRH delta hdelta
    refine ⟨0, le_rfl, fun n hnN hnE => ?_⟩
    have hpos :=
      (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
    simpa [xiRectangularWeilLogCoefficient] using hpos
  · exact riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff_transverse
      hL hN E hE

/-- **Exact transverse thickness law under false RH.** If all non-subpower negative excursions
are confined to `E`, then the exceptional carrier has divergent Dirichlet energy at the exact
sharp transverse exponent on at least one line to the right of one. -/
theorem exists_transverseExceptionalEnergy_divergence_of_not_riemannHypothesis
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hlower : XiRectangularWeilSubpowerLowerOff L N E)
    (hnot : ¬ RiemannHypothesis) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ¬ LSeriesSummable
        (fun n => ((xiRectangularPowerExceptionalCoefficient
          xiRightTransverseSup E n : ℝ) : ℂ))
        (((1 + epsilon : ℝ) : ℂ)) := by
  by_contra hdiv
  push Not at hdiv
  have hE : XiRectangularTransverseExceptionalEnergy E := by
    intro epsilon hepsilon
    exact hdiv epsilon hepsilon
  exact hnot
    (riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff_transverse
      hL hN E hE hlower)

end

end RHTower
