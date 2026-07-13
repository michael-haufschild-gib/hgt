import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedSurvivalTransform

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The even completed tail potential whose decreasing half-line profile differentiates to the
completed survival remainder. -/
def thetaCuspCompletedTailPotential (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-x / 2) - thetaCuspTailDerivative 0 x

theorem thetaCuspCompletedTailPotential_neg (x : ℝ) :
    thetaCuspCompletedTailPotential (-x) =
      thetaCuspCompletedTailPotential x := by
  unfold thetaCuspCompletedTailPotential
  rw [thetaCuspTailDerivative_zero_neg]
  ring_nf

theorem hasDerivAt_thetaCuspCompletedTailPotential (x : ℝ) :
    HasDerivAt thetaCuspCompletedTailPotential
      (-(1 / 4 : ℝ) * thetaCuspCompletedSurvivalRemainder x) x := by
  unfold thetaCuspCompletedTailPotential
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t / 2))
      (-(1 / 2 : ℝ) * Real.exp (-x / 2)) x := by
    convert (Real.hasDerivAt_exp (-x / 2)).comp x
      ((hasDerivAt_neg x).div_const 2) using 1
    ring_nf
  convert (hexp.const_mul (1 / 2 : ℝ)).sub
    (hasDerivAt_thetaCuspTailDerivative 0 x) using 1
  unfold thetaCuspCompletedSurvivalRemainder thetaCuspTailSurvival
  norm_num
  ring_nf

/-- The completed potential is the Green primitive of the negative even theta-cusp source. -/
theorem thetaCuspCompletedTailPotential_secondOperator_eq_neg_fullSource
    (x : ℝ) :
    (1 / 8 : ℝ) * Real.exp (-x / 2) -
          thetaCuspTailDerivative 2 x -
        (1 / 4 : ℝ) * thetaCuspCompletedTailPotential x =
      -thetaCuspFullSource x := by
  rw [thetaCuspFullSource_eq_tail_second_sub]
  unfold thetaCuspCompletedTailPotential
  ring

theorem thetaCuspCompletedTailPotential_tendsto_atTop_zero :
    Tendsto thetaCuspCompletedTailPotential atTop (nhds 0) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (nhds 0) := by
    have hlin : Tendsto (fun x : ℝ => -x / 2) atTop atBot := by
      have h := tendsto_id.const_mul_atTop_of_neg
        (by norm_num : (-1 / 2 : ℝ) < 0)
      convert h using 1
      funext x
      simp only [id_eq]
      ring_nf
    exact Real.tendsto_exp_atBot.comp hlin
  have htail : Tendsto (thetaCuspTailDerivative 0) atTop (nhds 0) := by
    simpa using pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero 0 0
  unfold thetaCuspCompletedTailPotential
  simpa using (hexp.const_mul (1 / 2 : ℝ)).sub htail

theorem thetaCuspCompletedTailPotential_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspCompletedTailPotential x := by
  have hanti : AntitoneOn thetaCuspCompletedTailPotential (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_thetaCuspCompletedTailPotential t).continuousAt).continuousOn
    · exact fun t _ht =>
        (hasDerivAt_thetaCuspCompletedTailPotential t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hasDerivAt_thetaCuspCompletedTailPotential t).deriv]
      have ht0 : 0 ≤ t := by
        have : 0 < t := by simpa [interior_Ici] using ht
        exact this.le
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num : -(1 / 4 : ℝ) ≤ 0)
        (thetaCuspCompletedSurvivalRemainder_nonneg ht0)
  have hevent : ∀ᶠ y : ℝ in atTop,
      thetaCuspCompletedTailPotential y ≤ thetaCuspCompletedTailPotential x :=
    eventually_atTop.2 ⟨x, fun y hy => hanti hx (hx.trans hy) hy⟩
  exact le_of_tendsto thetaCuspCompletedTailPotential_tendsto_atTop_zero hevent

def thetaCuspCompletedSurvivalValueTransform
    (d : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspCompletedSurvivalRemainder x : ℂ) *
      thetaCuspTailSecondCoreAtomSourceDerivative d z x

def thetaCuspCompletedSurvivalMonomial (d : ℕ) (z : ℂ) : ℂ :=
  (-4 * z ^ 2) ^ (d + 1)

def thetaCuspCompletedSurvivalMonomialDerivative
    (d : ℕ) (z : ℂ) : ℂ :=
  -8 * ((d + 1 : ℕ) : ℂ) * z * (-4 * z ^ 2) ^ d

theorem xiCTaylorThetaTailCorePolynomial_eval_eq_completedSurvival
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).eval z =
      (1 / 2 : ℂ) *
        (thetaCuspCompletedSurvivalMonomial d z -
          thetaCuspCompletedSurvivalValueTransform d z) := by
  rw [xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral,
    integral_density_mul_coreAtom_eq_pow_sub_completedSurvival]
  rfl

theorem hasDerivAt_thetaCuspCompletedSurvivalMonomial
    (d : ℕ) (z : ℂ) :
    HasDerivAt (thetaCuspCompletedSurvivalMonomial d)
      (thetaCuspCompletedSurvivalMonomialDerivative d z) z := by
  have hbase : HasDerivAt (fun w : ℂ => -4 * w ^ 2) (-8 * z) z := by
    convert (hasDerivAt_const z (-4 : ℂ)).mul ((hasDerivAt_id z).pow 2) using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have hp := hbase.pow (d + 1)
  unfold thetaCuspCompletedSurvivalMonomial
    thetaCuspCompletedSurvivalMonomialDerivative
  convert hp using 1
  rw [show d + 1 - 1 = d by omega]
  push_cast
  ring

def thetaCuspCompletedSurvivalDerivativeTransform
    (d : ℕ) (z : ℂ) : ℂ :=
  thetaCuspCompletedSurvivalMonomialDerivative d z -
    2 * (xiCTaylorThetaTailCorePolynomial d).derivative.eval z

theorem thetaCuspCompletedSurvivalValueTransform_eq_monomial_sub_two_core
    (d : ℕ) (z : ℂ) :
    thetaCuspCompletedSurvivalValueTransform d z =
      thetaCuspCompletedSurvivalMonomial d z -
        2 * (xiCTaylorThetaTailCorePolynomial d).eval z := by
  have h := xiCTaylorThetaTailCorePolynomial_eval_eq_completedSurvival d z
  linear_combination 2 * h

/-- The derivative of the completed survival integral is identified from its exact finite
polynomial value relation, without a differentiation-under-the-integral assumption. -/
theorem hasDerivAt_thetaCuspCompletedSurvivalValueTransform
    (d : ℕ) (z : ℂ) :
    HasDerivAt (thetaCuspCompletedSurvivalValueTransform d)
      (thetaCuspCompletedSurvivalDerivativeTransform d z) z := by
  have hfun : thetaCuspCompletedSurvivalValueTransform d =
      fun w : ℂ => thetaCuspCompletedSurvivalMonomial d w -
        2 * (xiCTaylorThetaTailCorePolynomial d).eval w := by
    funext w
    exact thetaCuspCompletedSurvivalValueTransform_eq_monomial_sub_two_core d w
  rw [hfun]
  unfold thetaCuspCompletedSurvivalDerivativeTransform
  convert (hasDerivAt_thetaCuspCompletedSurvivalMonomial d z).sub
    ((xiCTaylorThetaTailCorePolynomial d).hasDerivAt z |>.const_mul 2) using 1

theorem xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_completedSurvival
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).derivative.eval z =
      (1 / 2 : ℂ) *
        (thetaCuspCompletedSurvivalMonomialDerivative d z -
          thetaCuspCompletedSurvivalDerivativeTransform d z) := by
  unfold thetaCuspCompletedSurvivalDerivativeTransform
  ring

/-- Exact monomial--remainder polarization of the finite theta-tail core current. -/
theorem xiCTaylorThetaTailCore_current_eq_completedSurvival_mixed
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ((thetaCuspCompletedSurvivalMonomialDerivative d z -
            thetaCuspCompletedSurvivalDerivativeTransform d z) *
          (starRingEnd ℂ)
            (thetaCuspCompletedSurvivalMonomial d z -
              thetaCuspCompletedSurvivalValueTransform d z)).im := by
  unfold orientedPolynomialCurrent
  rw [xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_completedSurvival,
    xiCTaylorThetaTailCorePolynomial_eval_eq_completedSurvival, map_mul]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    rw [map_div₀, map_one, map_ofNat]]
  rw [show ((1 / 2 : ℂ) *
      (thetaCuspCompletedSurvivalMonomialDerivative d z -
        thetaCuspCompletedSurvivalDerivativeTransform d z)) *
      ((1 / 2 : ℂ) * (starRingEnd ℂ)
        (thetaCuspCompletedSurvivalMonomial d z -
          thetaCuspCompletedSurvivalValueTransform d z)) =
      (1 / 4 : ℂ) *
        ((thetaCuspCompletedSurvivalMonomialDerivative d z -
            thetaCuspCompletedSurvivalDerivativeTransform d z) *
          (starRingEnd ℂ)
            (thetaCuspCompletedSurvivalMonomial d z -
              thetaCuspCompletedSurvivalValueTransform d z)) by ring]
  rw [Complex.mul_im]
  norm_num

end

end RHTower
