import GaloisForLFunctions.RHTower.CCM.CCMRectangularObservablePowerLowerZeroFree
import GaloisForLFunctions.RHTower.CCM.CCMRectangularTransverseGrowth
import GaloisForLFunctions.RHTower.CCM.CCMRectangularFullObservableDivisorTomography

/-!
# The exact one-sided transverse exponent of the CCM rectangular observable

For a fixed positive window width, consider the actual logarithmically sampled Xi--Weil
observable.  This module identifies all exponents for which its negative part admits an eventual
polynomial budget.  They form exactly the upper ray beginning at the supremal displacement of the
right Xi divisor.

Equivalently, for every nonnegative `alpha`, an eventual loss budget of order `n ^ alpha` exists
if and only if every Xi zero lies in the half-plane `re rho <= 1 / 2 + alpha`.  This statement is
unconditional: when RH holds, positivity supplies the zero budget; when RH fails, the quantitative
Landau theorem and the sharp transverse growth bound give the two implications.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The admissible one-sided power-floor exponents of the actual fixed-window sequence form
exactly the upper ray starting at the supremal right transverse Xi displacement. -/
theorem xiRectangularWeilTailPowerLower_iff_transverseSup_le
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hne : Nonempty XiRightZeroCopy) :
    (∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
      XiRectangularWeilTailPowerLower L N alpha) ↔
      xiRightTransverseSup ≤ alpha := by
  constructor
  · rintro ⟨N, hN, hlower⟩
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact xiRightCenteredZero_re_le_of_xiRectangularWeilTailPowerLower
      hL halpha0 hN hlower q
  · intro hsup
    obtain ⟨N, hN⟩ := exists_xiRectangularAdmissibleCutoff L
    let K : ℝ :=
      2 * xiRectangularRightCoefficientNormSum L +
        rectangularTwoEdgeRemainderBound L *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
    have hK : 0 ≤ K := by
      dsimp only [K]
      exact add_nonneg
        (mul_nonneg (by norm_num)
          (tsum_nonneg fun q : XiRightZeroCopy => norm_nonneg _))
        (mul_nonneg
          (by unfold rectangularTwoEdgeRemainderBound; positivity)
          (tsum_nonneg fun q : XiZeroCopy => by positivity))
    refine ⟨N, hN, K, hK, ?_⟩
    intro n hnN
    obtain ⟨hn1, hLa⟩ := hN n hnN
    have hn0 : n ≠ 0 := by omega
    have hnorm :=
      norm_xiWeilPolarization_rectangular_logSample_le_transverse_power
        hne hn1 hLa
    have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hpow : (n : ℝ) ^ xiRightTransverseSup ≤ (n : ℝ) ^ alpha :=
      Real.rpow_le_rpow_of_exponent_le hbase hsup
    have hre :
        -‖xiRectangularWeilLogCoefficient L n‖ ≤
          (xiRectangularWeilLogCoefficient L n).re :=
      (neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _)
    rw [powerCorrectionCoefficient, if_neg hn0]
    dsimp only [xiRectangularWeilLogCoefficient] at hnorm hre ⊢
    nlinarith [mul_le_mul_of_nonneg_left hpow hK]

/-- Quantitative lower-loss tomography: for every nonnegative exponent, an eventual lower floor
of that order exists exactly when the full right Xi divisor lies in the corresponding horizontal
half-plane. -/
theorem xiRectangularWeilTailPowerLower_iff_all_rightZeros_le
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hne : Nonempty XiRightZeroCopy) :
    (∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
      XiRectangularWeilTailPowerLower L N alpha) ↔
      ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ alpha := by
  rw [xiRectangularWeilTailPowerLower_iff_transverseSup_le hL halpha0 hne]
  constructor
  · intro hsup q
    exact (xiRightCenteredZero_re_le_sup q).trans hsup
  · intro hq
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact hq q

/-- Full zero-free-region form, with no assumption that an off-line zero exists: an eventual
one-sided loss budget of order `n ^ alpha` for the actual fixed-window observable exists exactly
when every Xi zero lies in `re rho <= 1/2 + alpha`. -/
theorem xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) :
    (∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
      XiRectangularWeilTailPowerLower L N alpha) ↔
      ∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha := by
  constructor
  · rintro ⟨N, hN, hlower⟩ rho hzero
    exact xi_zero_re_le_half_add_of_xiRectangularWeilTailPowerLower
      hL halpha0 hN hlower hzero
  · intro hzeros
    by_cases hRH : RiemannHypothesis
    · obtain ⟨N, hN⟩ := exists_xiRectangularAdmissibleCutoff L
      refine ⟨N, hN, 0, le_rfl, ?_⟩
      intro n _hnN
      simp only [zero_mul, add_zero]
      exact (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform_squareSummable L (Real.log n / 2))
    · have hne : Nonempty XiRightZeroCopy :=
        nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
      apply (xiRectangularWeilTailPowerLower_iff_all_rightZeros_le
        hL halpha0 hne).2
      intro q
      have hz : xi (q.1.1 : ℂ) = 0 :=
        xi_eq_zero_of_mem_divisor_support q.1.1
      have hq := hzeros (q.1.1 : ℂ) hz
      rw [xiRightCenteredZero_eq_support_sub_half]
      norm_num [Complex.sub_re] at hq ⊢
      linarith

/-- Equivalent open-half-plane form of the exact one-sided exponent law. -/
theorem xiRectangularWeilTailPowerLower_iff_xi_zeroFree_right_halfPlane
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) :
    (∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
      XiRectangularWeilTailPowerLower L N alpha) ↔
      ∀ rho : ℂ, 1 / 2 + alpha < rho.re → xi rho ≠ 0 := by
  rw [xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le hL halpha0]
  constructor
  · intro hzeros rho hrho hzero
    exact (not_lt_of_ge (hzeros rho hzero)) hrho
  · intro hzeroFree rho hzero
    exact le_of_not_gt fun hrho => hzeroFree rho hrho hzero

/-- Global transverse-supremum form.  The empty right-divisor case is included: then RH holds,
the supremum is zero, and the observable has the zero loss budget. -/
theorem xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha) :
    (∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
      XiRectangularWeilTailPowerLower L N alpha) ↔
      xiRightTransverseSup ≤ alpha := by
  by_cases hne : Nonempty XiRightZeroCopy
  · exact xiRectangularWeilTailPowerLower_iff_transverseSup_le hL halpha0 hne
  · letI : IsEmpty XiRightZeroCopy := ⟨fun q => hne ⟨q⟩⟩
    have hRH : RiemannHypothesis := by
      by_contra hnot
      exact hne (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot)
    have hp : ∃ N : ℕ,
        (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
        XiRectangularWeilTailPowerLower L N alpha := by
      obtain ⟨N, hN⟩ := exists_xiRectangularAdmissibleCutoff L
      refine ⟨N, hN, 0, le_rfl, ?_⟩
      intro n _hnN
      simp only [zero_mul, add_zero]
      exact (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform_squareSummable L (Real.log n / 2))
    have hsup0 : xiRightTransverseSup = 0 := by
      rw [xiRightTransverseSup, xiRightTransverseSet]
      have hrange : Set.range (fun q : XiRightZeroCopy =>
          (xiRightCenteredZero q).re) = ∅ := Set.range_eq_empty_iff.mpr inferInstance
      rw [hrange, Real.sSup_empty]
    exact iff_of_true hp (hsup0.le.trans halpha0)

/-- The spectrum of admissible one-sided polynomial loss exponents for a fixed CCM window. -/
def xiRectangularOneSidedExponentSet (L : ℝ) : Set ℝ :=
  {alpha : ℝ | 0 ≤ alpha ∧
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
      XiRectangularWeilTailPowerLower L N alpha}

/-- Exact exponent-spectrum theorem: the admissible one-sided loss exponents form the closed
upper ray whose endpoint is the supremal right transverse Xi displacement. -/
theorem xiRectangularOneSidedExponentSet_eq_Ici_transverseSup
    {L : ℝ} (hL : 0 < L) :
    xiRectangularOneSidedExponentSet L = Set.Ici xiRightTransverseSup := by
  ext alpha
  constructor
  · rintro ⟨halpha0, hfloor⟩
    exact (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
      hL halpha0).1 hfloor
  · intro hsup
    have hsup0 : 0 ≤ xiRightTransverseSup := by
      by_cases hne : Nonempty XiRightZeroCopy
      · exact (xiRightTransverseSup_pos hne).le
      · letI : IsEmpty XiRightZeroCopy := ⟨fun q => hne ⟨q⟩⟩
        rw [xiRightTransverseSup, xiRightTransverseSet]
        have hrange : Set.range (fun q : XiRightZeroCopy =>
            (xiRightCenteredZero q).re) = ∅ := Set.range_eq_empty_iff.mpr inferInstance
        rw [hrange, Real.sSup_empty]
    have halpha0 : 0 ≤ alpha := hsup0.trans hsup
    exact ⟨halpha0,
      (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
        hL halpha0).2 hsup⟩

end

end RHTower
