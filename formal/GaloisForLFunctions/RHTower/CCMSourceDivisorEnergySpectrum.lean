import GaloisForLFunctions.RHTower.CCMCriticalMellinDivisorTomography
import GaloisForLFunctions.RHTower.CCMRectangularFiniteChannelNonDilution

/-!
# Quantitative prime-source, critical-Mellin, and Weil-energy spectrum

The complete inverse-tilted prime source, the intrinsic critical-Mellin defect, and the negative
fixed-window Weil carrier encode the same horizontal Xi zero-free region.  This module states that
identification at every transverse width `alpha`, rather than only at the RH endpoint `alpha = 0`.

It also closes the infinite-channel loophole in the form that is actually valid.  A finite exact
positive split conserves the carrier abscissa in one channel.  An arbitrary pointwise-summable
positive family need not have such a channel, but its aggregate coefficient still dominates the
carrier and therefore pays the complete transverse abscissa.  Thus the horizontal exponent can be
distributed only by retaining it in the summable aggregate.
-/

open Complex Filter Function Set LSeries

noncomputable section

namespace RHTower

set_option maxHeartbeats 1000000

/-- Every Xi zero lies to the left of the transverse line `Re rho = 1/2 + alpha`. -/
def XiZeroHalfPlaneBound (alpha : ℝ) : Prop :=
  ∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha

/-- The complete inverse-tilted dyadic prime source is holomorphic strictly to the right of its
shifted transverse line. -/
def InverseTiltedDyadicSourceAnalyticAbove (alpha : ℝ) : Prop :=
  ∀ s : ℂ, 1 + alpha < s.re →
    AnalyticAt ℂ inverseTiltedDyadicContinuedSource s

/-- The intrinsic critical-Mellin defect is holomorphic strictly to the right of the translated
transverse line. -/
def CriticalMellinDefectAnalyticAbove (alpha : ℝ) : Prop :=
  ∀ u : ℂ, alpha - 1 / 2 < u.re →
    AnalyticAt ℂ regularizedCriticalMellinDefect u

/-- Quantitative source tomography: the explicit inverse-tilted prime source is holomorphic above
`1 + alpha` exactly when every Xi zero lies left of `1/2 + alpha`. -/
theorem xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiZeroHalfPlaneBound alpha ↔
      InverseTiltedDyadicSourceAnalyticAbove alpha := by
  constructor
  · intro hzeros s hs
    have hsHalf : 1 / 2 < s.re := by linarith
    apply analyticAt_inverseTiltedDyadicContinuedSource_of_regularizedZeta_ne_zero hsHalf
    intro hzero
    obtain ⟨rho, hrho⟩ :=
      exists_xiDivisorSupport_of_inverseTilted_regularizedZeta_zero hsHalf hzero
    have hbound := hzeros (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)
    have hre := congrArg Complex.re hrho
    rw [inverseTiltedXiPole, Complex.add_re] at hre
    norm_num at hre
    linarith
  · intro han rho hzero
    by_contra hnot
    have hrho : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
    let zrho : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    let p : ℂ := inverseTiltedXiPole zrho
    have hp : 1 + alpha < p.re := by
      dsimp only [p, inverseTiltedXiPole, zrho]
      rw [Complex.add_re]
      norm_num
      linarith
    have hpOrder :
        meromorphicOrderAt inverseTiltedDyadicContinuedSource p =
          ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one zrho
    have hpNonneg := (han p hp).meromorphicOrderAt_nonneg
    rw [hpOrder] at hpNonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hpNonneg

/-- Quantitative intrinsic tomography: the regularized critical-Mellin defect is holomorphic above
`alpha - 1/2` exactly when every Xi zero lies left of `1/2 + alpha`. -/
theorem xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiZeroHalfPlaneBound alpha ↔
      CriticalMellinDefectAnalyticAbove alpha := by
  constructor
  · intro hzeros u hu
    have huNegOne : -1 < u.re := by linarith
    apply analyticAt_regularizedCriticalMellinDefect_of_regularizedZeta_ne_zero huNegOne
    intro hzero
    obtain ⟨rho, hrho⟩ :=
      exists_xiDivisorSupport_of_criticalMellin_regularizedZeta_zero huNegOne hzero
    have hbound := hzeros (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)
    have hre := congrArg Complex.re hrho
    rw [criticalMellinXiPole, Complex.sub_re] at hre
    norm_num at hre
    linarith
  · intro han rho hzero
    by_contra hnot
    have hrho : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
    let zrho : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    let u : ℂ := criticalMellinXiPole zrho
    have hu : alpha - 1 / 2 < u.re := by
      dsimp only [u, criticalMellinXiPole, zrho]
      rw [Complex.sub_re]
      norm_num
      linarith
    have huOrder :
        meromorphicOrderAt regularizedCriticalMellinDefect u =
          ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one zrho
    have huNonneg := (han u hu).meromorphicOrderAt_nonneg
    rw [huOrder] at huNonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) huNonneg

/-- The global Xi half-plane bound is exactly the intrinsic fixed-window negative-energy law. -/
theorem xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiZeroHalfPlaneBound alpha ↔
      XiRectangularNegativeChannelEnergyAbove alpha
        (xiRectangularWeilTailNegativePart L N) := by
  have hzeroSup :
      XiZeroHalfPlaneBound alpha ↔ xiRightTransverseSup ≤ alpha := by
    constructor
    · intro hzeros
      exact (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
        hL halpha).1
          ((xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
            hL halpha).2 hzeros)
    · intro hsup
      exact (xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
        hL halpha).1
          ((xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
            hL halpha).2 hsup)
  exact hzeroSup.trans
    (xiRightTransverseSup_le_iff_negativePartEnergyAbove hL halpha hN)

/-- A pointwise-summable positive channel family together with its aggregate coefficient.  The
aggregate may cover rather than exactly equal the negative Weil carrier. -/
structure XiRectangularSummableNegativeChannelCover
    (ι : Type*) (L : ℝ) (N : ℕ) (a : ι → ℕ → ℝ) (total : ℕ → ℝ) : Prop where
  channel_nonneg : ∀ i n, 0 ≤ a i n
  channel_hasSum : ∀ n, HasSum (fun i => a i n) (total n)
  carrier_le_total : ∀ n, xiRectangularWeilTailNegativePart L N n ≤ total n

/-- The aggregate of a pointwise-summable nonnegative channel family is nonnegative. -/
theorem XiRectangularSummableNegativeChannelCover.total_nonneg
    {ι : Type*} {L : ℝ} {N : ℕ} {a : ι → ℕ → ℝ} {total : ℕ → ℝ}
    (hcover : XiRectangularSummableNegativeChannelCover ι L N a total)
    (n : ℕ) :
    0 ≤ total n := by
  rw [← (hcover.channel_hasSum n).tsum_eq]
  exact tsum_nonneg fun i => hcover.channel_nonneg i n

/-- **Summable-family aggregate non-dilution.**  For an arbitrary pointwise-summable positive
channel cover, the aggregate coefficient has absolute-convergence abscissa at least that of the
negative Weil carrier. -/
theorem summableNegativeChannelCover_aggregate_forces_full_abscissa
    {ι : Type*} {L : ℝ} {N : ℕ} {a : ι → ℕ → ℝ} {total : ℕ → ℝ}
    (hcover : XiRectangularSummableNegativeChannelCover ι L N a total) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) ≤
      LSeries.abscissaOfAbsConv
        (rectangularNegativeChannelCoefficient total) := by
  apply abscissaOfAbsConv_le_of_nonnegative_domination
  · exact xiRectangularWeilTailNegativePart_nonneg L N
  · exact hcover.total_nonneg
  · exact hcover.carrier_le_total

/-- Under false RH, the aggregate of every pointwise-summable positive channel cover pays the
complete shifted transverse-divisor abscissa. -/
theorem summableNegativeChannelCover_aggregate_forces_transverseSup_of_not_rh
    {ι : Type*} {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis)
    {a : ι → ℕ → ℝ} {total : ℕ → ℝ}
    (hcover : XiRectangularSummableNegativeChannelCover ι L N a total) :
    ((1 + xiRightTransverseSup : ℝ) : EReal) ≤
      LSeries.abscissaOfAbsConv
        (rectangularNegativeChannelCoefficient total) := by
  rw [← xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
    hL hN hnot]
  exact summableNegativeChannelCover_aggregate_forces_full_abscissa hcover

/-- **Summable-family zero-free-region theorem.**  If the aggregate of one pointwise-summable
positive channel cover has abscissa at most `1 + alpha`, every Xi zero lies to the left of
`1/2 + alpha`. -/
theorem xiZeroHalfPlaneBound_of_summableNegativeChannelCover_aggregate_abscissa
    {ι : Type*} {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a : ι → ℕ → ℝ} {total : ℕ → ℝ}
    (hcover : XiRectangularSummableNegativeChannelCover ι L N a total)
    (htotal :
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient total) ≤
        ((1 + alpha : ℝ) : EReal)) :
    XiZeroHalfPlaneBound alpha := by
  apply (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove
    hL halpha hN).2
  intro epsilon hepsilon
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  have hcarrier :=
    (summableNegativeChannelCover_aggregate_forces_full_abscissa hcover).trans htotal
  have hstrict :
      ((1 + alpha : ℝ) : EReal) <
        ((1 + alpha + epsilon : ℝ) : EReal) := by
    exact_mod_cast (by linarith : 1 + alpha < 1 + alpha + epsilon)
  simpa only [ofReal_re] using! hcarrier.trans_lt hstrict

/-- At the critical aggregate abscissa, one pointwise-summable positive channel cover proves RH. -/
theorem riemannHypothesis_of_summableNegativeChannelCover_aggregate_abscissa_le_one
    {ι : Type*} {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a : ι → ℕ → ℝ} {total : ℕ → ℝ}
    (hcover : XiRectangularSummableNegativeChannelCover ι L N a total)
    (htotal :
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient total) ≤
        ((1 : ℝ) : EReal)) :
    RiemannHypothesis := by
  have hzeros : XiZeroHalfPlaneBound 0 :=
    xiZeroHalfPlaneBound_of_summableNegativeChannelCover_aggregate_abscissa
      hL (show (0 : ℝ) ≤ 0 by rfl) hN hcover (by
        simpa only [add_zero] using htotal)
  apply rh_iff_xi_ne_zero_right.mpr
  intro rho hrho hzero
  have hbound := hzeros rho hzero
  rw [mem_rightHalf] at hrho
  norm_num at hbound
  linarith

/-- **Principal quantitative conservation theorem.**  At every transverse width `alpha`, the Xi
zero-free half-plane, the complete prime-source half-plane, the intrinsic critical-Mellin
half-plane, and the fixed-window negative-energy law are the same datum. -/
theorem ccmQuantitativeSourceDivisorEnergySpectrum_capstone
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiZeroHalfPlaneBound alpha ↔
      InverseTiltedDyadicSourceAnalyticAbove alpha ∧
      CriticalMellinDefectAnalyticAbove alpha ∧
      XiRectangularNegativeChannelEnergyAbove alpha
        (xiRectangularWeilTailNegativePart L N) := by
  constructor
  · intro hzeros
    exact ⟨
      (xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove halpha).1 hzeros,
      (xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove halpha).1 hzeros,
      (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove hL halpha hN).1 hzeros⟩
  · rintro ⟨_hsource, _hcritical, henergy⟩
    exact (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove hL halpha hN).2 henergy

/-- The endpoint `alpha = 0` of the quantitative conservation theorem is exactly RH. -/
theorem riemannHypothesis_iff_ccmSourceDivisorEnergyEndpoint
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      InverseTiltedDyadicSourceAnalyticAbove 0 ∧
      CriticalMellinDefectAnalyticAbove 0 ∧
      XiRectangularNegativeChannelEnergyAbove 0
        (xiRectangularWeilTailNegativePart L N) := by
  have hzero :
      RiemannHypothesis ↔ XiZeroHalfPlaneBound 0 := by
    constructor
    · intro hRH rho hzero
      have hre := (riemannHypothesis_iff_inverseTiltedDyadic_poles_on_line.mp hRH)
        (inverseTiltedXiPole ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩)
        (inverseTiltedXiPole_re_gt_half
          ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩)
        (meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one
          ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩)
      rw [inverseTiltedXiPole, Complex.add_re] at hre
      norm_num at hre ⊢
      linarith
    · intro hzeros
      apply rh_iff_xi_ne_zero_right.mpr
      intro rho hrho hzero
      have hbound := hzeros rho hzero
      rw [mem_rightHalf] at hrho
      norm_num at hbound
      linarith
  exact hzero.trans
    (ccmQuantitativeSourceDivisorEnergySpectrum_capstone
      hL (show (0 : ℝ) ≤ 0 by rfl) hN)

end RHTower
