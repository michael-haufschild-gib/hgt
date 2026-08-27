import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicExactWronskianConservation

/-!
# Exact BM second-harmonic AdS forbidden solution

The change of variable `w = 1-z` turns the original BM Gauss equation into a Gauss equation with
outer parameter `a+b+1-c = 1/2`. Its regular hypergeometric series gives the actual constant
(forbidden) AdS branch, with two real derivatives and exact radial-jet annihilation on `0<z<1`.
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries Polynomial

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Gauss parameter of the constant outer branch after `w=1-z`. -/
def d4BMPlusPlusAdSForbiddenHypergeometricC
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
    d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1 -
    d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)

/-- Universal outer exponent balance: the constant branch has parameter `1/2`. -/
theorem d4BMPlusPlusAdSForbiddenHypergeometricC_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusAdSForbiddenHypergeometricC n chi = 1 / 2 := by
  rw [d4BMPlusPlusAdSForbiddenHypergeometricC]
  linear_combination d4BMPlusPlusHypergeometric_exponentBalance n chi

/-- Nonzero angular real part excludes all terminating collisions of the outer constant series. -/
theorem d4BMPlusPlusAdSForbiddenHypergeometricParameters_ne_negNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠
        -d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi ∧
      (j : ℂ) ≠
        -d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi ∧
      (j : ℂ) ≠ -d4BMPlusPlusAdSForbiddenHypergeometricC n chi := by
  rcases d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi j with
    ⟨ha, hb, _⟩
  refine ⟨ha, hb, ?_⟩
  rw [d4BMPlusPlusAdSForbiddenHypergeometricC_eq]
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
  linarith

/-- Formal series of the constant AdS outer branch in `w=1-z`. -/
def d4BMPlusPlusAdSForbiddenHypergeometricSeries
    (n : ℕ) (chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ
    (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMPlusPlusAdSForbiddenHypergeometricC n chi)

/-- Exact unit radius of the outer constant series. -/
theorem d4BMPlusPlusAdSForbiddenHypergeometricSeries_radius_eq_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi).radius = 1 := by
  rw [d4BMPlusPlusAdSForbiddenHypergeometricSeries]
  apply ordinaryHypergeometricSeries_radius_eq_one
  exact d4BMPlusPlusAdSForbiddenHypergeometricParameters_ne_negNat n chi hchi

/-- Analytic outer constant factor as a function of `w=1-z`. -/
def d4BMPlusPlusAdSForbiddenHypergeometricFactor
    (n : ℕ) (chi w : ℂ) : ℂ :=
  (d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi).sum w

/-- First `w` derivative-series value of the outer constant factor. -/
def d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative
    (n : ℕ) (chi w : ℂ) : ℂ :=
  (((d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi).derivSeries.sum w) 1)

/-- Second `w` derivative-series value of the outer constant factor. -/
def d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative
    (n : ℕ) (chi w : ℂ) : ℂ :=
  ((((d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi).derivSeries.derivSeries.sum w)
    1) 1)

@[simp]
theorem d4BMPlusPlusAdSForbiddenHypergeometricFactor_zero
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi 0 = 1 := by
  change ordinaryHypergeometric
    (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMPlusPlusAdSForbiddenHypergeometricC n chi) 0 = 1
  exact ordinaryHypergeometric_zero _ _ _

/-- Exact first analytic derivative of the outer constant factor. -/
theorem hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFactor
    (n : ℕ) (chi w : ℂ) (hchi : chi.re ≠ 0) (hw : ‖w‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi)
      (d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi w) w := by
  let p := d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi
  have hwp : ‖w‖ₑ < p.radius := by
    rw [d4BMPlusPlusAdSForbiddenHypergeometricSeries_radius_eq_one n chi hchi]
    exact hw
  change HasDerivAt p.sum ((p.derivSeries.sum w) 1) w
  exact (p.hasFDerivAt_sum hwp).hasDerivAt

/-- Exact second analytic derivative of the outer constant factor. -/
theorem hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative
    (n : ℕ) (chi w : ℂ) (hchi : chi.re ≠ 0) (hw : ‖w‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi)
      (d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi w) w := by
  let p := d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi
  let q := p.derivSeries
  have hwp : ‖w‖ₑ < p.radius := by
    rw [d4BMPlusPlusAdSForbiddenHypergeometricSeries_radius_eq_one n chi hchi]
    exact hw
  have hwq : ‖w‖ₑ < q.radius :=
    lt_of_lt_of_le hwp p.radius_le_radius_derivSeries
  have hq := q.hasFDerivAt_sum hwq
  have heval := hq.clm_apply (hasFDerivAt_const (1 : ℂ) w)
  change HasDerivAt (fun u : ℂ => (q.sum u) 1)
    (((q.derivSeries.sum w) 1) 1) w
  simpa using heval.hasDerivAt

/-- Reversing the independent variable transforms the outer Gauss jet into the original jet. -/
theorem gaussJet_one_sub_transform
    (a b c z F dF ddF : ℂ) :
    z * (1 - z) * ddF +
        (c - (a + b + 1) * z) * (-dF) - a * b * F =
      (1 - z) * z * ddF +
        ((a + b + 1 - c) - (a + b + 1) * (1 - z)) * dF - a * b * F := by
  ring

/-- The analytic outer constant factor satisfies its transformed Gauss equation. -/
theorem d4BMPlusPlusAdSForbiddenHypergeometric_standardGaussODE
    (n : ℕ) (chi w : ℂ) (hchi : chi.re ≠ 0) (hw : ‖w‖ₑ < 1) :
    w * (1 - w) *
          d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi w +
        (d4BMPlusPlusAdSForbiddenHypergeometricC n chi -
          (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
            d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1) * w) *
          d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi w -
      d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
        d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi *
          d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi w = 0 := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMPlusPlusAdSForbiddenHypergeometricC n chi
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := by
    intro j
    exact (d4BMPlusPlusAdSForbiddenHypergeometricParameters_ne_negNat
      n chi hchi j).2.2
  have hwr : ‖w‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    change ‖w‖ₑ < (d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi).radius
    rw [d4BMPlusPlusAdSForbiddenHypergeometricSeries_radius_eq_one n chi hchi]
    exact hw
  simpa [a, b, c, d4BMPlusPlusAdSForbiddenHypergeometricFactor,
    d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative,
    d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative,
    d4BMPlusPlusAdSForbiddenHypergeometricSeries,
    ordinaryHypergeometricFirstDerivativeSeriesValue,
    ordinaryHypergeometricSecondDerivativeSeriesValue] using
      ordinaryHypergeometric_standardGaussODE a b c w hc hwr

/-- Constant AdS branch as a function of original radius `z`. -/
def d4BMPlusPlusAdSForbiddenSolution
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi ((1 - z : ℝ) : ℂ)

/-- Exact first radial derivative of the constant AdS branch. -/
def d4BMPlusPlusAdSForbiddenSolutionDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  -d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi ((1 - z : ℝ) : ℂ)

/-- Exact second radial derivative of the constant AdS branch. -/
def d4BMPlusPlusAdSForbiddenSolutionSecondDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi ((1 - z : ℝ) : ℂ)

/-- First outer solution jet is its actual derivative on the radial interior. -/
theorem hasDerivAt_d4BMPlusPlusAdSForbiddenSolution
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSForbiddenSolution n chi)
      (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z) z := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw1 : 1 - z < 1 := by linarith
  have hF :=
    hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFactor
      n chi ((1 - z : ℝ) : ℂ) hchi (enorm_ofReal_lt_one hw0 hw1)
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hcomp := hF.comp z hinner.ofReal_comp
  change HasDerivAt
    (fun x : ℝ => d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
      ((1 - x : ℝ) : ℂ))
    (-d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
      ((1 - z : ℝ) : ℂ)) z
  simpa [Function.comp_def] using! hcomp

/-- Second outer solution jet differentiates the first on the radial interior. -/
theorem hasDerivAt_d4BMPlusPlusAdSForbiddenSolutionDerivative
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi)
      (d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z) z := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw1 : 1 - z < 1 := by linarith
  have hF :=
    hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative
      n chi ((1 - z : ℝ) : ℂ) hchi (enorm_ofReal_lt_one hw0 hw1)
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hcomp := (hF.comp z hinner.ofReal_comp).neg
  change HasDerivAt
    (fun x : ℝ => -d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
      ((1 - x : ℝ) : ℂ))
    (d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi
      ((1 - z : ℝ) : ℂ)) z
  simpa [Function.comp_def] using! hcomp

/-- The exact constant AdS branch solves the original BM radial equation. -/
theorem d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusAdSForbiddenSolution n chi z)
      (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z)
      (d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z) = 0 := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw1 : 1 - z < 1 := by linarith
  have hode := d4BMPlusPlusAdSForbiddenHypergeometric_standardGaussODE
    n chi ((1 - z : ℝ) : ℂ) hchi (enorm_ofReal_lt_one hw0 hw1)
  rw [d4BMPlusPlusHypergeometricJet,
    d4BMPlusPlusAdSForbiddenSolution,
    d4BMPlusPlusAdSForbiddenSolutionDerivative,
    d4BMPlusPlusAdSForbiddenSolutionSecondDerivative]
  push_cast
  rw [gaussJet_one_sub_transform]
  rw [show
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
          d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1 -
        d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) =
      d4BMPlusPlusAdSForbiddenHypergeometricC n chi by
        rfl]
  convert hode using 1
  all_goals push_cast
  all_goals ring

/-- Every Xi fibre carries the exact constant AdS outer solution jet. -/
theorem d4BMXiPlusPlusAdSForbiddenSolution_jet_eq_zero
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n (d4BMXiMixedHorizonAngularMomentum q) z
      (d4BMPlusPlusAdSForbiddenSolution n
        (d4BMXiMixedHorizonAngularMomentum q) z)
      (d4BMPlusPlusAdSForbiddenSolutionDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z)
      (d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z) = 0 :=
  d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1

end

end RHTower
