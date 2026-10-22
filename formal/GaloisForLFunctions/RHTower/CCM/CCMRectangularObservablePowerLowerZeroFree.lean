import GaloisForLFunctions.RHTower.CCM.CCMRectangularPowerLowerZeroFree

/-!
# An observable rectangular power floor gives a Xi zero-free region

The fixed-exponent divisor-carrier theorem becomes a source-facing statement after absorbing the
bounded rectangular Weil remainder.  An eventual lower floor of order `n ^ α` for one actual
rectangular Weil family forces every Xi zero into `re ρ ≤ 1 / 2 + α`.

Unlike the all-epsilon subpower capstone, this module retains the exponent and therefore records a
quantitative horizontal zero-free region.
-/

open Complex

namespace RHTower

noncomputable section

/-- An eventual one-sided power floor for the actual observable rectangular Weil values. -/
def XiRectangularWeilTailPowerLower (L : ℝ) (N : ℕ) (alpha : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
    0 ≤ (xiRectangularWeilLogCoefficient L n).re +
      C * powerCorrectionCoefficient alpha n

/-- The bounded rectangular remainder transports an observable power floor to a global floor for
the positive-transverse divisor carrier. -/
theorem exists_xiRectangularRightPowerLower_of_xiRectangularWeilTailPowerLower
    {L alpha : ℝ} (halpha0 : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlower : XiRectangularWeilTailPowerLower L N alpha) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        D * powerCorrectionCoefficient alpha n := by
  obtain ⟨C, hC, hobs⟩ := hlower
  let B : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg
    (by unfold rectangularTwoEdgeRemainderBound; positivity)
    (tsum_nonneg fun q => by positivity)
  have hevent : ∀ n : ℕ, N ≤ n → n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        (C + B) * powerCorrectionCoefficient alpha n := by
    intro n hnN hn0
    obtain ⟨hn1, _hLa⟩ := hN n hnN
    have hremNorm := norm_xiRectangularWeilRemainderCoefficient_le hN n
    have hremRe :
        (xiRectangularWeilRemainderCoefficient L N n).re ≤ B :=
      (Complex.re_le_norm _).trans hremNorm
    have hremEq : xiRectangularWeilRemainderCoefficient L N n =
        xiRectangularWeilLogCoefficient L n -
          (xiRectangularRightDirichletCoefficientReal L n : ℂ) := by
      rw [xiRectangularWeilRemainderCoefficient,
        xiRectangularWeilTailCoefficient, if_pos hnN,
        xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hnN), add_zero,
        ofReal_xiRectangularRightDirichletCoefficientReal]
    have hremReEq := congrArg Complex.re hremEq
    simp only [Complex.sub_re, ofReal_re] at hremReEq
    have hpone : 1 ≤ powerCorrectionCoefficient alpha n := by
      rw [powerCorrectionCoefficient, if_neg hn0]
      exact Real.one_le_rpow (by exact_mod_cast hn1) halpha0
    have hobsn := hobs n hnN
    nlinarith [mul_le_mul_of_nonneg_left hpone hB]
  exact exists_global_power_lower_of_eventual
    (fun n => xiRectangularRightDirichletCoefficientReal L n)
    halpha0 (add_nonneg hC hB) hevent

/-- An observable fixed-power floor bounds every positive-transverse Xi zero by that exponent. -/
theorem xiRightCenteredZero_re_le_of_xiRectangularWeilTailPowerLower
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlower : XiRectangularWeilTailPowerLower L N alpha)
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  obtain ⟨D, _hD, hglobal⟩ :=
    exists_xiRectangularRightPowerLower_of_xiRectangularWeilTailPowerLower
      halpha0 hN hlower
  exact xiRightCenteredZero_re_le_of_xiRectangularRightPowerLower
    hL halpha0 ⟨q⟩ hglobal q

/-- The same observable floor bounds the centered real coordinate of every multiplicity copy of a
Xi zero.  Copies on or to the left of the critical line satisfy the bound from `α ≥ 0`; copies on
the right are controlled by the quantitative Landau theorem. -/
theorem re_I_mul_xiSpectralPoint_le_of_xiRectangularWeilTailPowerLower
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlower : XiRectangularWeilTailPowerLower L N alpha)
    (q : XiZeroCopy) :
    (I * xiSpectralPoint q).re ≤ alpha := by
  by_cases hright : 0 < (I * xiSpectralPoint q).re
  · let qr : XiRightZeroCopy := ⟨q, hright⟩
    simpa only [xiRightCenteredZero] using
      xiRightCenteredZero_re_le_of_xiRectangularWeilTailPowerLower
        hL halpha0 hN hlower qr
  · exact (le_of_not_gt hright).trans halpha0

/-- Quantitative source-facing zero-free theorem: an eventual observable lower loss `O(n^α)`
forces every Xi zero into the half-plane `re ρ ≤ 1/2 + α`. -/
theorem xi_zero_re_le_half_add_of_xiRectangularWeilTailPowerLower
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlower : XiRectangularWeilTailPowerLower L N alpha)
    {rho : ℂ} (hzero : xi rho = 0) :
    rho.re ≤ 1 / 2 + alpha := by
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support support
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hn⟩⟩
  have hq := re_I_mul_xiSpectralPoint_le_of_xiRectangularWeilTailPowerLower
    hL halpha0 hN hlower q
  have hcoord : I * xiSpectralPoint q = rho - 1 / 2 := by
    simpa only [q, support] using I_mul_xiSpectralPoint q
  rw [hcoord] at hq
  norm_num [Complex.sub_re] at hq ⊢
  linarith

/-- Equivalent zero-free-half-plane form of the quantitative observable theorem. -/
theorem xi_ne_zero_of_half_add_alpha_lt_re_of_xiRectangularWeilTailPowerLower
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlower : XiRectangularWeilTailPowerLower L N alpha)
    {rho : ℂ} (hrho : 1 / 2 + alpha < rho.re) :
    xi rho ≠ 0 := by
  intro hzero
  have := xi_zero_re_le_half_add_of_xiRectangularWeilTailPowerLower
    hL halpha0 hN hlower hzero
  linarith

end

end RHTower
