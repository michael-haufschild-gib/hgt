import GaloisForLFunctions.RHTower.CCMRectangularSubpowerLowerGate

/-!
# A one-sided rectangular power floor gives a zero-free half-plane

The all-epsilon subpower gate proves RH.  This module retains the exponent:
an eventual lower correction of order `n ^ α` bounds the positive transverse
Xi divisor by `α`.  It reuses the power-corrected Landau continuation and does
not introduce another coefficient or continuation surface.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- A global one-sided power floor for the positive-transverse rectangular
coefficient bounds its entire transverse supremum by the same exponent. -/
theorem xiRightTransverseSup_le_of_xiRectangularRightPowerLower
    {L alpha C : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hne : Nonempty XiRightZeroCopy)
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        C * powerCorrectionCoefficient alpha n) :
    xiRightTransverseSup ≤ alpha := by
  by_contra hnot
  have halphaDelta : alpha < xiRightTransverseSup := lt_of_not_ge hnot
  obtain ⟨sigma, hsigmaAlpha, hsigmaDelta, hsumPower⟩ :=
    exists_xiRectangularPowerLandauCoefficient_summable_left_of_boundary
      L C alpha hne halphaDelta hlower
  have hsigma : 1 < sigma := by linarith
  have hpower : LSeriesSummable
      (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply powerCorrectionCoefficient_LSeriesSummable
    simpa only [ofReal_re] using hsigmaAlpha
  have hscaled := hpower.smul (C : ℂ)
  have hdiff := hsumPower.sub hscaled
  have horiginal : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    apply hdiff.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        xiRectangularPowerLandauCoefficient, if_neg hn0,
        xiRectangularLandauCoefficient, if_pos (Nat.zero_le n)]
      push_cast
      ring
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_landau_summable hL 0 0 hsigma
      (xiRightTransverseSup_pos hne).le
      (fun q => xiRightCenteredZero_re_le_sup q) horiginal
  have hcenterBound : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ sigma - 1 := by
    intro q
    have hq := hpoleBound q
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hq
    linarith
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 := by
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact hcenterBound q
  linarith

/-- The same fixed-exponent floor gives the corresponding zero-free region
for every positive-transverse Xi zero copy. -/
theorem xiRightCenteredZero_re_le_of_xiRectangularRightPowerLower
    {L alpha C : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hne : Nonempty XiRightZeroCopy)
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        C * powerCorrectionCoefficient alpha n)
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  exact (xiRightCenteredZero_re_le_sup q).trans
    (xiRightTransverseSup_le_of_xiRectangularRightPowerLower
      hL halpha0 hne hlower)

end

end RHTower
