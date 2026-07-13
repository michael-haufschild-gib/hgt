import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowEnergySpectrum
import GaloisForLFunctions.RHTower.CCMRectangularFiniteChannelNonDilution
import GaloisForLFunctions.RHTower.CCMSourceDivisorEnergySpectrum

/-!
# The sharp-prime negative channel is the least positive correction

The dyadic sharp prime source is signed.  A positive-channel realization must add a
nonnegative correction which makes every corrected source coefficient nonnegative.
This file proves that the negative part of the source is the pointwise least such
correction.  By the exact sharp-window identity, that least correction is precisely
twice the positive excess of the weighted dyadic prime window.

Consequently every positive correction dominates the canonical RH-bearing channel,
both pointwise and at the level of absolute-convergence abscissa.  Summability of any
such correction at `1 + alpha` therefore gives the corresponding Xi zero-free region;
critical all-epsilon summability, or abscissa at most one, proves RH.
-/

open Complex Filter Function Set LSeries

noncomputable section

namespace RHTower

/-- A nonnegative correction which makes the signed dyadic sharp-prime source
coefficientwise nonnegative. -/
def DyadicSharpPrimePositiveCorrection (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
    ∀ n, 0 ≤ dyadicSharpPrimeSourceCoefficient n + a n

/-- The canonical negative-part correction is admissible. -/
theorem dyadicSharpPrimeSourceNegativePart_isPositiveCorrection :
    DyadicSharpPrimePositiveCorrection dyadicSharpPrimeSourceNegativePart := by
  constructor
  · exact dyadicSharpPrimeSourceNegativePart_nonneg
  · exact dyadicSharpNegativePartLandauCoefficient_nonneg

/-- **Pointwise minimality.**  Every nonnegative correction which makes the sharp source
nonnegative dominates its negative part. -/
theorem dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a) (n : ℕ) :
    dyadicSharpPrimeSourceNegativePart n ≤ a n := by
  rw [dyadicSharpPrimeSourceNegativePart, negPart_def]
  exact max_le (by linarith [ha.2 n]) (ha.1 n)

/-- The admissible sharp-source corrections have a least element in pointwise order. -/
theorem dyadicSharpPrimeSourceNegativePart_isLeastPositiveCorrection :
    DyadicSharpPrimePositiveCorrection dyadicSharpPrimeSourceNegativePart ∧
      ∀ a : ℕ → ℝ, DyadicSharpPrimePositiveCorrection a →
        ∀ n, dyadicSharpPrimeSourceNegativePart n ≤ a n :=
  ⟨dyadicSharpPrimeSourceNegativePart_isPositiveCorrection,
    fun _ ha n =>
      dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection ha n⟩

/-- Every admissible positive correction pays at least twice the exact dyadic-window
positive excess. -/
theorem two_mul_dyadicWeightedPrimeWindowPositiveExcess_le_of_positiveCorrection
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a) (n : ℕ) :
    2 * dyadicWeightedPrimeWindowPositiveExcess n ≤ a n := by
  rw [← dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess]
  exact dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection ha n

/-- In particular, every admissible correction dominates the positive excess itself. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_le_of_positiveCorrection
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a) (n : ℕ) :
    dyadicWeightedPrimeWindowPositiveExcess n ≤ a n := by
  have hpay :=
    two_mul_dyadicWeightedPrimeWindowPositiveExcess_le_of_positiveCorrection ha n
  have hnonneg := dyadicWeightedPrimeWindowPositiveExcess_nonneg n
  linarith

/-- **Abscissa optimality.**  The canonical correction has the least absolute-convergence
abscissa among all nonnegative corrections which make the sharp source positive. -/
theorem dyadicSharpPrimeSourceNegativePart_abscissa_le_of_positiveCorrection
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a) :
    LSeries.abscissaOfAbsConv
        (rectangularNegativeChannelCoefficient dyadicSharpPrimeSourceNegativePart) ≤
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient a) := by
  apply abscissaOfAbsConv_le_of_nonnegative_domination
  · exact dyadicSharpPrimeSourceNegativePart_nonneg
  · exact ha.1
  · exact fun n =>
      dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection ha n

/-- The attainable abscissa sublevel sets of all admissible corrections are exactly the
sublevel sets of the canonical negative-part correction. -/
theorem exists_dyadicSharpPositiveCorrection_abscissa_le_iff
    (x : EReal) :
    (∃ a : ℕ → ℝ,
        DyadicSharpPrimePositiveCorrection a ∧
          LSeries.abscissaOfAbsConv
              (rectangularNegativeChannelCoefficient a) ≤ x) ↔
      LSeries.abscissaOfAbsConv
          (rectangularNegativeChannelCoefficient
            dyadicSharpPrimeSourceNegativePart) ≤ x := by
  constructor
  · rintro ⟨a, ha, habscissa⟩
    exact
      (dyadicSharpPrimeSourceNegativePart_abscissa_le_of_positiveCorrection ha).trans
        habscissa
  · intro habscissa
    exact ⟨dyadicSharpPrimeSourceNegativePart,
      dyadicSharpPrimeSourceNegativePart_isPositiveCorrection, habscissa⟩

/-- A summable admissible correction gives the same quantitative Xi zero-free region as
the canonical prime-window positive excess. -/
theorem xi_zero_re_le_half_add_of_dyadicSharpPositiveCorrection_summable
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a)
    (hsum : LSeriesSummable
      (rectangularNegativeChannelCoefficient a)
      (((1 + alpha : ℝ) : ℂ)))
    {rho : ℂ} (hzero : xi rho = 0) :
    rho.re ≤ 1 / 2 + alpha := by
  apply xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
    halpha
  · apply LSeriesSummable_of_nonneg_of_le
      dyadicWeightedPrimeWindowPositiveExcess_nonneg ha.1
      (dyadicWeightedPrimeWindowPositiveExcess_le_of_positiveCorrection ha)
    exact hsum
  · exact hzero

/-- Critical all-epsilon summability of any admissible positive correction proves RH. -/
theorem riemannHypothesis_of_dyadicSharpPositiveCorrectionEnergy
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a)
    (henergy : ∀ epsilon : ℝ, 0 < epsilon →
      LSeriesSummable
        (rectangularNegativeChannelCoefficient a)
        (((1 + epsilon : ℝ) : ℂ))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  apply LSeriesSummable_of_nonneg_of_le
    dyadicWeightedPrimeWindowPositiveExcess_nonneg ha.1
    (dyadicWeightedPrimeWindowPositiveExcess_le_of_positiveCorrection ha)
  exact henergy epsilon hepsilon

/-- Existence of a critical-energy admissible correction is equivalent to critical energy
of the canonical negative channel.  Thus introducing auxiliary positive channels cannot
weaken the analytic burden. -/
theorem exists_dyadicSharpPositiveCorrectionEnergy_iff_negativePartEnergy :
    (∃ a : ℕ → ℝ,
        DyadicSharpPrimePositiveCorrection a ∧
          ∀ epsilon : ℝ, 0 < epsilon →
            LSeriesSummable
              (rectangularNegativeChannelCoefficient a)
              (((1 + epsilon : ℝ) : ℂ))) ↔
      DyadicSharpPrimeSourceNegativePartEnergy := by
  constructor
  · rintro ⟨a, ha, henergy⟩
    intro epsilon hepsilon
    apply LSeriesSummable_of_nonneg_of_le
      dyadicSharpPrimeSourceNegativePart_nonneg ha.1
      (dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection ha)
    exact henergy epsilon hepsilon
  · intro henergy
    exact ⟨dyadicSharpPrimeSourceNegativePart,
      dyadicSharpPrimeSourceNegativePart_isPositiveCorrection, henergy⟩

/-- **Quantitative correction-abscissa law.**  If any admissible positive correction has
absolute-convergence abscissa at most `1 + alpha`, then every Xi zero lies in
`Re rho ≤ 1/2 + alpha`. -/
theorem xiZeroHalfPlaneBound_of_dyadicSharpPositiveCorrection_abscissa
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a)
    (habscissa :
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient a) ≤
        ((1 + alpha : ℝ) : EReal)) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hzero
  by_contra hnot
  have hgap : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
  let epsilon : ℝ := (rho.re - (1 / 2 + alpha)) / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hsum : LSeriesSummable
      (rectangularNegativeChannelCoefficient a)
      (((1 + (alpha + epsilon) : ℝ) : ℂ)) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    have hstrict :
        ((1 + alpha : ℝ) : EReal) <
          ((1 + (alpha + epsilon) : ℝ) : EReal) := by
      exact_mod_cast (by linarith : 1 + alpha < 1 + (alpha + epsilon))
    simpa only [ofReal_re] using habscissa.trans_lt hstrict
  have hbound :=
    xi_zero_re_le_half_add_of_dyadicSharpPositiveCorrection_summable
      (by linarith : 0 ≤ alpha + epsilon) ha hsum hzero
  dsimp only [epsilon] at hbound
  linarith

/-- An admissible positive correction of absolute-convergence abscissa at most one proves RH. -/
theorem riemannHypothesis_of_dyadicSharpPositiveCorrection_abscissa_le_one
    {a : ℕ → ℝ} (ha : DyadicSharpPrimePositiveCorrection a)
    (habscissa :
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient a) ≤
        ((1 : ℝ) : EReal)) :
    RiemannHypothesis := by
  have hzeros : XiZeroHalfPlaneBound 0 :=
    xiZeroHalfPlaneBound_of_dyadicSharpPositiveCorrection_abscissa
      (show (0 : ℝ) ≤ 0 by rfl) ha (by
        simpa only [add_zero] using habscissa)
  apply rh_iff_xi_ne_zero_right.mpr
  intro rho hrho hzero
  have hbound := hzeros rho hzero
  rw [mem_rightHalf] at hrho
  norm_num at hbound
  linarith

/-- **Minimal-correction capstone.**  The sharp-prime source has a canonical least positive
correction, it equals twice the dyadic-window excess, and every other admissible correction
has no smaller absolute-convergence abscissa. -/
theorem dyadicSharpPrimeMinimalPositiveCorrection_capstone :
    DyadicSharpPrimePositiveCorrection dyadicSharpPrimeSourceNegativePart ∧
      (∀ n, dyadicSharpPrimeSourceNegativePart n =
        2 * dyadicWeightedPrimeWindowPositiveExcess n) ∧
      ∀ a : ℕ → ℝ, DyadicSharpPrimePositiveCorrection a →
        (∀ n, dyadicSharpPrimeSourceNegativePart n ≤ a n) ∧
          LSeries.abscissaOfAbsConv
              (rectangularNegativeChannelCoefficient
                dyadicSharpPrimeSourceNegativePart) ≤
            LSeries.abscissaOfAbsConv
              (rectangularNegativeChannelCoefficient a) := by
  refine ⟨dyadicSharpPrimeSourceNegativePart_isPositiveCorrection,
    dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess, ?_⟩
  intro a ha
  exact ⟨dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection ha,
    dyadicSharpPrimeSourceNegativePart_abscissa_le_of_positiveCorrection ha⟩

end RHTower
