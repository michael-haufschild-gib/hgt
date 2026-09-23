import GaloisForLFunctions.HilbertMetric.FifthRootAtomLikelihoodRiccatiNoGo

/-!
# Increasing Riccati charge does not force global fifth-root curvature

The completed-theta C5 reduction exposes the conjugated Riccati charge
`exp(2q) * (2q'q'' - q''')`. Its strict increase has the wrong orientation for the required
upper envelope. This module closes that potential workaround: the existing sextic Gaussian
countermodel has the same charge strictly increasing from zero, a globally nonnegative Riccati
margin, positive C5 next to the seam, and negative C5 later. Combined with the imported
`atomLikelihoodRiccatiSignArchitecture_with_localC5_does_not_force_globalC5`, the same profile
also retains the full six-jet atom/likelihood sign architecture.

Therefore lower drift, charge positivity, or charge monotonicity cannot close C5. Any surviving
proof must compare the literal completed-theta charge to a nonlocal source-history upper envelope.
-/

open Set

namespace HilbertMetric

noncomputable section

/-- Integrating-factor Riccati charge of the sextic Gaussian C5 countermodel. -/
def sexticGaussianRiccatiCharge (t : ℝ) : ℝ :=
  Real.exp (2 * sexticGaussianAction t) *
    (2 * sexticGaussianActionOne t * sexticGaussianActionTwo t -
      sexticGaussianActionThree t)

private theorem sexticGaussianRiccatiChargeDerivativeCore_pos (t : ℝ) :
    0 < 2 * sexticGaussianActionTwo t ^ (2 : ℕ) +
      4 * sexticGaussianActionOne t ^ (2 : ℕ) * sexticGaussianActionTwo t -
      sexticGaussianActionFour t := by
  let x : ℝ := t ^ (2 : ℕ)
  let a : ℝ := 4 + 4 / 5 * x + 6 * x ^ (2 : ℕ)
  let b : ℝ := 4 + 12 / 5 * x + 30 * x ^ (2 : ℕ)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have ha : 4 ≤ a := by
    dsimp [a]
    nlinarith [sq_nonneg x]
  have hb : 4 ≤ b := by
    dsimp [b]
    nlinarith [sq_nonneg x]
  have haSq : 16 ≤ a ^ (2 : ℕ) := by nlinarith [sq_nonneg (a - 4)]
  have hab : 64 ≤ a ^ (2 : ℕ) * b := by
    have h₁ : 64 ≤ 16 * b := by nlinarith
    have h₂ : 16 * b ≤ a ^ (2 : ℕ) * b :=
      mul_le_mul_of_nonneg_right haSq (by positivity)
    linarith
  have hlarge : 256 * x ≤ 4 * x * a ^ (2 : ℕ) * b := by
    have := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 4 * x)
    nlinarith
  have hquad :
      0 < 136 / 5 - 328 / 5 * x + 12288 / 25 * x ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - (205 / 3072 : ℝ))]
  have hbase :
      0 < 136 / 5 - 1608 / 5 * x + 12288 / 25 * x ^ (2 : ℕ) +
          288 * x ^ (3 : ℕ) + 1800 * x ^ (4 : ℕ) + 256 * x := by
    have hx3 : 0 ≤ x ^ (3 : ℕ) := by positivity
    have hx4 : 0 ≤ x ^ (4 : ℕ) := by positivity
    nlinarith
  have hcore :
      0 <
        (136 / 5 - 1608 / 5 * x + 12288 / 25 * x ^ (2 : ℕ) +
          288 * x ^ (3 : ℕ) + 1800 * x ^ (4 : ℕ)) + 4 * x * a ^ (2 : ℕ) * b := by
    nlinarith
  have hidentity :
      2 * sexticGaussianActionTwo t ^ (2 : ℕ) +
          4 * sexticGaussianActionOne t ^ (2 : ℕ) * sexticGaussianActionTwo t -
          sexticGaussianActionFour t =
        (136 / 5 - 1608 / 5 * x + 12288 / 25 * x ^ (2 : ℕ) +
          288 * x ^ (3 : ℕ) + 1800 * x ^ (4 : ℕ)) + 4 * x * a ^ (2 : ℕ) * b := by
    dsimp [x, a, b]
    unfold sexticGaussianActionOne sexticGaussianActionTwo
      sexticGaussianActionFour
    ring_nf
  rw [hidentity]
  exact hcore

/-- Exact derivative of the conjugated Riccati charge. -/
theorem hasDerivAt_sexticGaussianRiccatiCharge (t : ℝ) :
    HasDerivAt sexticGaussianRiccatiCharge
      (Real.exp (2 * sexticGaussianAction t) *
        (2 * sexticGaussianActionTwo t ^ (2 : ℕ) +
          4 * sexticGaussianActionOne t ^ (2 : ℕ) * sexticGaussianActionTwo t -
          sexticGaussianActionFour t)) t := by
  have hExp := ((hasDerivAt_sexticGaussianAction t).const_mul 2).exp
  have hMarginRaw :=
    (((hasDerivAt_sexticGaussianActionOne t).mul
      (hasDerivAt_sexticGaussianActionTwo t)).const_mul 2).sub
      (hasDerivAt_sexticGaussianActionThree t)
  unfold sexticGaussianRiccatiCharge
  refine ((hExp.mul hMarginRaw).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [Pi.sub_apply, Pi.mul_apply]
    ring

theorem deriv_sexticGaussianRiccatiCharge_pos (t : ℝ) :
    0 < deriv sexticGaussianRiccatiCharge t := by
  rw [(hasDerivAt_sexticGaussianRiccatiCharge t).deriv]
  exact mul_pos (Real.exp_pos _) (sexticGaussianRiccatiChargeDerivativeCore_pos t)

theorem sexticGaussianRiccatiCharge_zero :
    sexticGaussianRiccatiCharge 0 = 0 := by
  norm_num [sexticGaussianRiccatiCharge, sexticGaussianAction,
    sexticGaussianActionOne, sexticGaussianActionTwo,
    sexticGaussianActionThree]

/-- The countermodel charge is strictly increasing from zero on the physical ray. -/
theorem strictMonoOn_sexticGaussianRiccatiCharge :
    StrictMonoOn sexticGaussianRiccatiCharge (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro t _
    exact (hasDerivAt_sexticGaussianRiccatiCharge t).continuousAt.continuousWithinAt
  · intro t _
    exact deriv_sexticGaussianRiccatiCharge_pos t

/-- **Charge-monotonicity no-go.** A smooth positive even reflected profile can have C5 positive
at the seam, a globally nonnegative Riccati margin, and a conjugated Riccati charge strictly
increasing from zero, yet have negative C5 later. The imported no-go proves the full six-jet
atom/likelihood sign architecture for this same profile. -/
theorem sexticGaussianRiccatiChargeMonotonicity_does_not_force_globalC5 :
    sexticGaussianRiccatiCharge 0 = 0 ∧
      StrictMonoOn sexticGaussianRiccatiCharge (Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 ≤ 2 * sexticGaussianActionOne t * sexticGaussianActionTwo t -
          sexticGaussianActionThree t) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
        0 < fifthRootDividedDropCurvatureNumerator
          sexticGaussianReflectedProfile t) ∧
      ∃ t : ℝ, 0 < t ∧
        fifthRootDividedDropCurvatureNumerator
          sexticGaussianReflectedProfile t < 0 := by
  refine ⟨sexticGaussianRiccatiCharge_zero,
    strictMonoOn_sexticGaussianRiccatiCharge, ?_,
    exists_sexticGaussianReflectedProfile_fifthRootCurvature_pos_right, ?_⟩
  · intro t ht
    exact sexticGaussianAction_riccatiMargin_nonneg ht
  · refine ⟨Real.sqrt (1 / 2), Real.sqrt_pos.2 (by norm_num), ?_⟩
    exact sexticGaussianReflectedProfile_fifthRootCurvature_neg

end

end HilbertMetric
