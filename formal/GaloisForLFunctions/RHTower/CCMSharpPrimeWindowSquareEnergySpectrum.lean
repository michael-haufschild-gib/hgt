import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareEnergySampling
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowEnergySpectrum

/-!
# The square-sampled positive-excess exponent bounds every Xi zero

The perfect-square reduction has an exact quantitative form.  If the dyadic positive excess at
`n = m^2` is summable with weight `m^(-1-2*alpha)`, then every Xi zero lies in
`Re rho <= 1/2 + alpha`.  Thus a specific off-line zero at transverse displacement `delta`
forces divergence of the square-sampled energy at every exponent strictly below `1 + 2*delta`.

This turns the former contradiction through `not RH` into a zero-by-zero source witness.  The
factor two is intrinsic: a mode of size `n^delta` has size `m^(2*delta)` on square apertures.
-/

open Complex LSeries

namespace RHTower

noncomputable section

/-- Positive-excess coefficient sampled only at perfect-square apertures. -/
def squarePrimeWindowPositiveExcessDirichletCoefficient (m : ℕ) : ℂ :=
  ((dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) : ℝ) : ℂ)

/-- Squared positive-excess coefficient sampled only at perfect-square apertures. -/
def squarePrimeWindowPositiveExcessSquareDirichletCoefficient (m : ℕ) : ℂ :=
  (((dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2 : ℝ) : ℂ)

/-- **Fixed-abscissa square-energy zero-free law.**  Critical square-sample energy at exponent
`1 + 2*alpha` places the complete Xi divisor in `Re rho <= 1/2 + alpha`. -/
theorem xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2))
        (1 + 2 * alpha)))
    {rho : ℂ} (hzero : xi rho = 0) :
    rho.re ≤ 1 / 2 + alpha := by
  apply xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
    halpha.le
  · exact dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareEnergy
      halpha hSquare
  · exact hzero

/-- **Sharp Hilbert-space square-energy zero-free law.**  Squaring the positive excess doubles
its growth exponent once more: weighted `L²` energy at `1 + 4*alpha` places every Xi zero in
`Re rho <= 1/2 + alpha`. -/
theorem xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessSquareEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2)
        (1 + 4 * alpha)))
    {rho : ℂ} (hzero : xi rho = 0) :
    rho.re ≤ 1 / 2 + alpha := by
  by_contra hnot
  have hrho : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
  let beta : ℝ := (alpha + (rho.re - 1 / 2)) / 2
  have halphaBeta : alpha < beta := by
    dsimp only [beta]
    linarith
  have hbetaRho : beta < rho.re - 1 / 2 := by
    dsimp only [beta]
    linarith
  have hbeta : 0 < beta := halpha.trans halphaBeta
  have hSquareLinear : LSeriesSummable
      (fun m => ((dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) : ℝ) : ℂ))
      (((1 + 2 * beta : ℝ) : ℂ)) := by
    apply LSeriesSummable_of_squareWeightedTerm_summable_at_lowerExponent
      (fun m => dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2))
      (squareSigma := 1 + 4 * alpha) (targetSigma := 1 + 2 * beta)
    · linarith
    · exact hSquare
  have hfull :=
    dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareLSeriesEnergy
      hbeta hSquareLinear
  have hbound :=
    xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
      hbeta.le hfull hzero
  linarith

/-- **Explicit square-energy witness from one off-line zero.**  If `rho` is a Xi zero and
`tau` is strictly below twice its transverse displacement, then the positive excess sampled at
perfect squares is not summable with weight `m^(-1-tau)`. -/
theorem not_squarePrimeWindowPositiveExcessEnergy_of_xi_zero_transverse
    {tau : ℝ} (htau : 0 < tau) {rho : ℂ} (hzero : xi rho = 0)
    (htransverse : tau < 2 * (rho.re - 1 / 2)) :
    ¬Summable
      (realDirichletWeightedTerm
        (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2))
        (1 + tau)) := by
  intro hSquare
  have hbound :=
    xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessEnergy
      (alpha := tau / 2) (by linarith) (by
        simpa only [show 1 + 2 * (tau / 2) = 1 + tau by ring] using hSquare)
      hzero
  linarith

/-- The same explicit witness in weighted `L²`: an off-line zero forces divergence of the
squared positive overshoot at every square-sample exponent below four times its displacement. -/
theorem not_squarePrimeWindowPositiveExcessSquareEnergy_of_xi_zero_transverse
    {tau : ℝ} (htau : 0 < tau) {rho : ℂ} (hzero : xi rho = 0)
    (htransverse : tau < 4 * (rho.re - 1 / 2)) :
    ¬Summable
      (realDirichletWeightedTerm
        (fun m => (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2)
        (1 + tau)) := by
  intro hSquare
  have hbound :=
    xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessSquareEnergy
      (alpha := tau / 4) (by linarith) (by
        simpa only [show 1 + 4 * (tau / 4) = 1 + tau by ring] using hSquare)
      hzero
  linarith

/-- **Square-sample abscissa tomography.**  Every right-half Xi zero `rho` forces the
absolute-convergence abscissa of the square-sampled positive excess to be at least
`2 * Re rho = 1 + 2 * (Re rho - 1/2)`.  This is the intrinsic exponent-doubling law. -/
theorem two_mul_xi_zero_re_le_squarePrimeWindowPositiveExcess_abscissa
    {rho : ℂ} (hzero : xi rho = 0) (hrho : 1 / 2 < rho.re) :
    (((2 * rho.re : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessDirichletCoefficient := by
  by_contra hnot
  have habslt :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient <
        (((2 * rho.re : ℝ) : EReal)) := lt_of_not_ge hnot
  have honeTarget : ((1 : ℝ) : EReal) < (((2 * rho.re : ℝ) : EReal)) := by
    exact_mod_cast (by linarith : (1 : ℝ) < 2 * rho.re)
  have hmax :
      max
          (LSeries.abscissaOfAbsConv
            squarePrimeWindowPositiveExcessDirichletCoefficient)
          ((1 : ℝ) : EReal) <
        (((2 * rho.re : ℝ) : EReal)) :=
    max_lt habslt honeTarget
  obtain ⟨sigma, hmaxSigma, hsigmaTarget⟩ :=
    EReal.exists_between_coe_real hmax
  have habsSigma :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient <
        (sigma : EReal) :=
    (le_max_left _ _).trans_lt hmaxSigma
  have honeSigma : (1 : ℝ) < sigma := by
    exact_mod_cast ((le_max_right
      (LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessDirichletCoefficient)
      ((1 : ℝ) : EReal)).trans_lt hmaxSigma)
  have hSquare : LSeriesSummable
      (fun m => ((dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) : ℝ) : ℂ))
      (sigma : ℂ) := by
    have hsum : LSeriesSummable
        squarePrimeWindowPositiveExcessDirichletCoefficient (sigma : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
        simpa only [ofReal_re] using habsSigma)
    simpa only [squarePrimeWindowPositiveExcessDirichletCoefficient] using! hsum
  let alpha : ℝ := (sigma - 1) / 2
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    linarith
  have hfull :=
    dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareLSeriesEnergy
      halpha (by
        simpa only [show 1 + 2 * alpha = sigma by
          dsimp only [alpha]
          ring] using hSquare)
  have hbound :=
    xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
      halpha.le hfull hzero
  have hsigmaTargetR : sigma < 2 * rho.re := by
    exact_mod_cast hsigmaTarget
  dsimp only [alpha] at hbound
  linarith

/-- **Hilbert square-sample abscissa tomography.**  Squaring the overshoot doubles the
transverse exponent again: every right-half Xi zero forces the squared-energy abscissa to be at
least `4 * Re rho - 1 = 1 + 4 * (Re rho - 1/2)`. -/
theorem four_mul_xi_zero_re_sub_one_le_squarePrimeWindowPositiveExcessSquare_abscissa
    {rho : ℂ} (hzero : xi rho = 0) (hrho : 1 / 2 < rho.re) :
    (((4 * rho.re - 1 : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient := by
  by_contra hnot
  have habslt :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient <
        (((4 * rho.re - 1 : ℝ) : EReal)) := lt_of_not_ge hnot
  have honeTarget :
      ((1 : ℝ) : EReal) < (((4 * rho.re - 1 : ℝ) : EReal)) := by
    exact_mod_cast (by linarith : (1 : ℝ) < 4 * rho.re - 1)
  have hmax :
      max
          (LSeries.abscissaOfAbsConv
            squarePrimeWindowPositiveExcessSquareDirichletCoefficient)
          ((1 : ℝ) : EReal) <
        (((4 * rho.re - 1 : ℝ) : EReal)) :=
    max_lt habslt honeTarget
  obtain ⟨sigma, hmaxSigma, hsigmaTarget⟩ :=
    EReal.exists_between_coe_real hmax
  have habsSigma :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient <
        (sigma : EReal) :=
    (le_max_left _ _).trans_lt hmaxSigma
  have honeSigma : (1 : ℝ) < sigma := by
    exact_mod_cast ((le_max_right
      (LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient)
      ((1 : ℝ) : EReal)).trans_lt hmaxSigma)
  have hSquareLSeries : LSeriesSummable
      (fun m => (((dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2 : ℝ) : ℂ))
      (sigma : ℂ) := by
    have hsum : LSeriesSummable
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient (sigma : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
        simpa only [ofReal_re] using habsSigma)
    simpa only [squarePrimeWindowPositiveExcessSquareDirichletCoefficient] using! hsum
  have hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2)
        sigma) :=
    realDirichletWeightedTerm_summable_of_LSeriesSummable
      (fun m => sq_nonneg (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)))
      hSquareLSeries
  let alpha : ℝ := (sigma - 1) / 4
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    linarith
  have hbound :=
    xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessSquareEnergy
      halpha (by
        simpa only [show 1 + 4 * alpha = sigma by
          dsimp only [alpha]
          ring] using hSquare)
      hzero
  have hsigmaTargetR : sigma < 4 * rho.re - 1 := by
    exact_mod_cast hsigmaTarget
  dsimp only [alpha] at hbound
  linarith

/-- **Global square-sample transverse spectrum.**  When the right transverse Xi divisor is
nonempty, its supremal displacement forces the full exponent-doubled lower bound for the
linear square-sampled positive-excess abscissa.  This statement uses the actual divisor
supremum directly and does not pass through `¬RiemannHypothesis`. -/
theorem one_add_two_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcess_abscissa
    (hne : Nonempty XiRightZeroCopy) :
    (((1 + 2 * xiRightTransverseSup : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessDirichletCoefficient := by
  by_contra hnot
  have habslt :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient <
        (((1 + 2 * xiRightTransverseSup : ℝ) : EReal)) :=
    lt_of_not_ge hnot
  have honeTarget :
      ((1 : ℝ) : EReal) <
        (((1 + 2 * xiRightTransverseSup : ℝ) : EReal)) := by
    exact_mod_cast (by linarith [xiRightTransverseSup_pos hne] :
      (1 : ℝ) < 1 + 2 * xiRightTransverseSup)
  have hmax :
      max
          (LSeries.abscissaOfAbsConv
            squarePrimeWindowPositiveExcessDirichletCoefficient)
          ((1 : ℝ) : EReal) <
        (((1 + 2 * xiRightTransverseSup : ℝ) : EReal)) :=
    max_lt habslt honeTarget
  obtain ⟨sigma, hmaxSigma, hsigmaTarget⟩ :=
    EReal.exists_between_coe_real hmax
  have habsSigma :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient <
        (sigma : EReal) :=
    (le_max_left _ _).trans_lt hmaxSigma
  have hsigmaTargetR : sigma < 1 + 2 * xiRightTransverseSup := by
    exact_mod_cast hsigmaTarget
  let alpha : ℝ := (sigma - 1) / 2
  have halphaSup : alpha < xiRightTransverseSup := by
    dsimp only [alpha]
    linarith
  obtain ⟨x, ⟨q, rfl⟩, hqAlpha⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty _) (by
      simpa only [xiRightTransverseSup, xiRightTransverseSet] using halphaSup)
  have hqSupport : sigma < 2 * (q.1.1 : ℂ).re := by
    change alpha < (xiRightCenteredZero q).re at hqAlpha
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hqAlpha
    norm_num at hqAlpha
    dsimp only [alpha] at hqAlpha
    linarith
  have hzero : xi (q.1.1 : ℂ) = 0 :=
    xi_eq_zero_of_mem_divisor_support q.1.1
  have hrho : 1 / 2 < (q.1.1 : ℂ).re := by
    have hpos := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hpos
    norm_num at hpos
    linarith
  have hqBound :=
    two_mul_xi_zero_re_le_squarePrimeWindowPositiveExcess_abscissa
      hzero hrho
  have hsigmaQ : (sigma : EReal) < (((2 * (q.1.1 : ℂ).re : ℝ) : EReal)) := by
    exact_mod_cast hqSupport
  exact (not_lt_of_ge hqBound) (habsSigma.trans hsigmaQ)

/-- **Global Hilbert square-sample transverse spectrum.**  Squaring the square-aperture
positive excess doubles the transverse exponent a second time, so its absolute-convergence
abscissa is at least `1 + 4 * xiRightTransverseSup`. -/
theorem one_add_four_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcessSquare_abscissa
    (hne : Nonempty XiRightZeroCopy) :
    (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient := by
  by_contra hnot
  have habslt :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient <
        (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) :=
    lt_of_not_ge hnot
  have honeTarget :
      ((1 : ℝ) : EReal) <
        (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) := by
    exact_mod_cast (by linarith [xiRightTransverseSup_pos hne] :
      (1 : ℝ) < 1 + 4 * xiRightTransverseSup)
  have hmax :
      max
          (LSeries.abscissaOfAbsConv
            squarePrimeWindowPositiveExcessSquareDirichletCoefficient)
          ((1 : ℝ) : EReal) <
        (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) :=
    max_lt habslt honeTarget
  obtain ⟨sigma, hmaxSigma, hsigmaTarget⟩ :=
    EReal.exists_between_coe_real hmax
  have habsSigma :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient <
        (sigma : EReal) :=
    (le_max_left _ _).trans_lt hmaxSigma
  have hsigmaTargetR : sigma < 1 + 4 * xiRightTransverseSup := by
    exact_mod_cast hsigmaTarget
  let alpha : ℝ := (sigma - 1) / 4
  have halphaSup : alpha < xiRightTransverseSup := by
    dsimp only [alpha]
    linarith
  obtain ⟨x, ⟨q, rfl⟩, hqAlpha⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty _) (by
      simpa only [xiRightTransverseSup, xiRightTransverseSet] using halphaSup)
  have hqSupport : sigma < 4 * (q.1.1 : ℂ).re - 1 := by
    change alpha < (xiRightCenteredZero q).re at hqAlpha
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hqAlpha
    norm_num at hqAlpha
    dsimp only [alpha] at hqAlpha
    linarith
  have hzero : xi (q.1.1 : ℂ) = 0 :=
    xi_eq_zero_of_mem_divisor_support q.1.1
  have hrho : 1 / 2 < (q.1.1 : ℂ).re := by
    have hpos := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hpos
    norm_num at hpos
    linarith
  have hqBound :=
    four_mul_xi_zero_re_sub_one_le_squarePrimeWindowPositiveExcessSquare_abscissa
      hzero hrho
  have hsigmaQ :
      (sigma : EReal) < (((4 * (q.1.1 : ℂ).re - 1 : ℝ) : EReal)) := by
    exact_mod_cast hqSupport
  exact (not_lt_of_ge hqBound) (habsSigma.trans hsigmaQ)

end

end RHTower
