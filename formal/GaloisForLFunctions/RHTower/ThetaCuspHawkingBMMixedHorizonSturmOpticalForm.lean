import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMProjectiveCausalResponse
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy

/-!
# Sturm optical form of the mixed Birmingham--Mokhtari horizon channel

At the exact mixed `+-` frequency and real horizon momentum, the two original hypergeometric
parameters are complex conjugates, the horizon parameter is the negative even integer `-N`, and

`a + b - c + 1 = 1/2`.

The hypergeometric radial operator consequently admits the real Sturm--Liouville multiplier

`p(z) = sqrt(1-z) / z^N`, `w(z) = p(z)/(z(1-z))`

on `0 < z < 1`. Its potential is `a b = |a|^(2 : ℕ) > 0`, and

`p'(z) = w(z) (-N + (N-1/2)z)`.

The final jet identity below is the exact gauge-independent radial Green identity input: every
phase in the mixed BM radial operator has paired into a squared modulus before any nonlinear
Einstein angular coupling is evaluated.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- First original hypergeometric parameter in the physical mixed channel. -/
def d4BMMixedHorizonSturmA (n k : ℕ) (chi : ℝ) : ℂ :=
  d4BMCausalHypergeometricA
    (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)

/-- Second original hypergeometric parameter in the physical mixed channel. -/
def d4BMMixedHorizonSturmB (n k : ℕ) (chi : ℝ) : ℂ :=
  d4BMCausalHypergeometricB
    (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)

/-- Mixed BM original hypergeometric parameters are conjugates. -/
theorem d4BMMixedHorizonSturmB_eq_conj_A
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonSturmB n k chi =
      starRingEnd ℂ (d4BMMixedHorizonSturmA n k chi) := by
  rw [d4BMMixedHorizonSturmA, d4BMMixedHorizonSturmB,
    d4BMCausalHypergeometricA_plusMinus,
    d4BMCausalHypergeometricB_plusMinus]
  norm_num [map_sub, map_add, map_neg, map_div₀, map_mul, map_ofNat,
    Complex.conj_I]
  ring

/-- Radial potential after conjugate pairing. -/
def d4BMMixedHorizonSturmPotential
    (n k : ℕ) (chi : ℝ) : ℝ :=
  Complex.normSq (d4BMMixedHorizonSturmA n k chi)

/-- Hypergeometric potential is exactly the real squared modulus. -/
theorem d4BMMixedHorizonSturmA_mul_B_eq_potential
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonSturmA n k chi *
        d4BMMixedHorizonSturmB n k chi =
      (d4BMMixedHorizonSturmPotential n k chi : ℂ) := by
  rw [d4BMMixedHorizonSturmB_eq_conj_A, Complex.mul_conj]
  rfl

/-- Mixed radial potential is strictly positive. -/
theorem d4BMMixedHorizonSturmPotential_pos
    (n k : ℕ) (chi : ℝ) :
    0 < d4BMMixedHorizonSturmPotential n k chi := by
  rw [d4BMMixedHorizonSturmPotential, Complex.normSq_pos]
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [d4BMMixedHorizonSturmA,
    d4BMCausalHypergeometricA_plusMinus] at hre
  norm_num at hre
  linarith

/-- Exact exponent balance producing the universal square-root outer-boundary factor. -/
theorem d4BMMixedHorizonSturm_exponentBalance
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonSturmA n k chi +
        d4BMMixedHorizonSturmB n k chi -
        d4BMCausalRadialC
          (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) + 1 =
      1 / 2 := by
  rw [d4BMMixedHorizonSturmA, d4BMMixedHorizonSturmB,
    d4BMCausalHypergeometricA_plusMinus,
    d4BMCausalHypergeometricB_plusMinus,
    d4BMCausalRadialC_plusMinus_eq_negNat]
  push_cast
  ring

/-- Real leading Sturm coefficient `p(z)`. -/
def d4BMMixedHorizonSturmP (n k : ℕ) (z : ℝ) : ℝ :=
  Real.sqrt (1 - z) / z ^ d4BMMixedHorizonFrobeniusOrder n k

/-- Positive integrating-factor weight `w(z)=p(z)/(z(1-z))`. -/
def d4BMMixedHorizonSturmWeight (n k : ℕ) (z : ℝ) : ℝ :=
  d4BMMixedHorizonSturmP n k z / (z * (1 - z))

/-- Real first-derivative coefficient of the mixed hypergeometric equation. -/
def d4BMMixedHorizonSturmDrift (n k : ℕ) (z : ℝ) : ℝ :=
  -(d4BMMixedHorizonFrobeniusOrder n k : ℝ) +
    ((d4BMMixedHorizonFrobeniusOrder n k : ℝ) - 1 / 2) * z

/-- Both Sturm multiplier and integrating weight are positive in the radial interior. -/
theorem d4BMMixedHorizonSturmP_pos_and_weight_pos
    (n k : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 < d4BMMixedHorizonSturmP n k z ∧
      0 < d4BMMixedHorizonSturmWeight n k z := by
  have hp : 0 < d4BMMixedHorizonSturmP n k z :=
    div_pos (Real.sqrt_pos.2 (sub_pos.mpr hz1))
      (pow_pos hz0 (d4BMMixedHorizonFrobeniusOrder n k))
  exact ⟨hp, div_pos hp (mul_pos hz0 (sub_pos.mpr hz1))⟩

/-- Exact derivative of the mixed BM Sturm multiplier. -/
theorem hasDerivAt_d4BMMixedHorizonSturmP
    (n k : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMMixedHorizonSturmP n k)
      (d4BMMixedHorizonSturmWeight n k z *
        d4BMMixedHorizonSturmDrift n k z) z := by
  let N := d4BMMixedHorizonFrobeniusOrder n k
  have hN : 0 < N := by
    simp [N, d4BMMixedHorizonFrobeniusOrder]
  have hz : z ≠ 0 := ne_of_gt hz0
  have h1z : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hsqrt0 : Real.sqrt (1 - z) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hz1))
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hsqrt := (Real.hasDerivAt_sqrt h1z).comp z hinner
  have hpow := hasDerivAt_pow N z
  refine (hsqrt.div hpow (pow_ne_zero N hz)).congr_deriv ?_
  rw [d4BMMixedHorizonSturmWeight, d4BMMixedHorizonSturmP,
    d4BMMixedHorizonSturmDrift]
  change _ = (_ / (z * (1 - z))) *
    (-(N : ℝ) + ((N : ℝ) - 1 / 2) * z)
  have hsquare : Real.sqrt (1 - z) ^ (2 : ℕ) = 1 - z :=
    Real.sq_sqrt (sub_nonneg.mpr (le_of_lt hz1))
  have hpowstep : z ^ N = z ^ (N - 1) * z := by
    conv_lhs => rw [← Nat.sub_add_cancel hN]
    rw [pow_succ]
  simp only [Function.comp_apply]
  field_simp
  rw [hpowstep, hsquare]
  ring

/-- Hypergeometric drift becomes the real Sturm drift. -/
theorem d4BMMixedHorizon_hypergeometricDrift_eq
    (n k : ℕ) (chi z : ℝ) :
    d4BMCausalRadialC
          (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) -
        (d4BMMixedHorizonSturmA n k chi +
          d4BMMixedHorizonSturmB n k chi + 1) * (z : ℂ) =
      (d4BMMixedHorizonSturmDrift n k z : ℂ) := by
  rw [d4BMMixedHorizonSturmA, d4BMMixedHorizonSturmB,
    d4BMCausalHypergeometricA_plusMinus,
    d4BMCausalHypergeometricB_plusMinus,
    d4BMCausalRadialC_plusMinus_eq_negNat]
  simp [d4BMMixedHorizonSturmDrift,
    d4BMMixedHorizonFrobeniusOrder]
  ring

/-- Hypergeometric differential expression evaluated on a second-order jet. -/
def d4BMMixedHorizonHypergeometricJet
    (n k : ℕ) (chi z : ℝ) (y dy ddy : ℂ) : ℂ :=
  (z * (1 - z) : ℝ) * ddy +
    (d4BMCausalRadialC
          (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) -
      (d4BMMixedHorizonSturmA n k chi +
        d4BMMixedHorizonSturmB n k chi + 1) * (z : ℂ)) * dy -
    d4BMMixedHorizonSturmA n k chi *
      d4BMMixedHorizonSturmB n k chi * y

/-- Exact Sturm--Liouville decomposition of the physical mixed BM radial jet. -/
theorem d4BMMixedHorizonHypergeometricJet_sturmDecomposition
    (n k : ℕ) (chi : ℝ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (y dy ddy : ℂ) :
    (d4BMMixedHorizonSturmWeight n k z : ℂ) *
        d4BMMixedHorizonHypergeometricJet n k chi z y dy ddy =
      (d4BMMixedHorizonSturmWeight n k z *
          d4BMMixedHorizonSturmDrift n k z : ℝ) * dy +
        (d4BMMixedHorizonSturmP n k z : ℂ) * ddy -
        (d4BMMixedHorizonSturmPotential n k chi *
          d4BMMixedHorizonSturmWeight n k z : ℝ) * y := by
  rw [d4BMMixedHorizonHypergeometricJet,
    d4BMMixedHorizon_hypergeometricDrift_eq,
    d4BMMixedHorizonSturmA_mul_B_eq_potential]
  have hzw : d4BMMixedHorizonSturmWeight n k z * (z * (1 - z)) =
      d4BMMixedHorizonSturmP n k z := by
    rw [d4BMMixedHorizonSturmWeight]
    field_simp [ne_of_gt hz0, ne_of_gt (sub_pos.mpr hz1)]
  have hzwC :
      (d4BMMixedHorizonSturmWeight n k z : ℂ) *
          ((z * (1 - z) : ℝ) : ℂ) =
        (d4BMMixedHorizonSturmP n k z : ℂ) := by
    exact_mod_cast hzw
  calc
    (d4BMMixedHorizonSturmWeight n k z : ℂ) *
        ((z * (1 - z) : ℝ) * ddy +
          (d4BMMixedHorizonSturmDrift n k z : ℂ) * dy -
          (d4BMMixedHorizonSturmPotential n k chi : ℂ) * y) =
      ((d4BMMixedHorizonSturmWeight n k z : ℂ) *
          (d4BMMixedHorizonSturmDrift n k z : ℂ)) * dy +
        ((d4BMMixedHorizonSturmWeight n k z : ℂ) *
          ((z * (1 - z) : ℝ) : ℂ)) * ddy -
        ((d4BMMixedHorizonSturmPotential n k chi : ℂ) *
          (d4BMMixedHorizonSturmWeight n k z : ℂ)) * y := by ring
    _ = _ := by
      rw [hzwC]
      push_cast
      ring

/-- Derivative jet of the real radial optical current
`p Im(conj(y) y')`. -/
def d4BMMixedHorizonOpticalCurrentDerivativeJet
    (n k : ℕ) (z : ℝ) (y dy ddy : ℂ) : ℝ :=
  (d4BMMixedHorizonSturmWeight n k z *
      d4BMMixedHorizonSturmDrift n k z) *
        ((starRingEnd ℂ y) * dy).im +
    d4BMMixedHorizonSturmP n k z *
      (((starRingEnd ℂ dy) * dy + (starRingEnd ℂ y) * ddy).im)

/-- Local optical theorem for the exact forced mixed BM radial equation. The positive real
potential contributes no imaginary flux; only the source pairing changes the horizon current. -/
theorem d4BMMixedHorizonOpticalCurrentDerivativeJet_eq_source
    (n k : ℕ) (chi : ℝ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (y dy ddy forcing : ℂ)
    (hforcing : d4BMMixedHorizonHypergeometricJet
      n k chi z y dy ddy = forcing) :
    d4BMMixedHorizonOpticalCurrentDerivativeJet n k z y dy ddy =
      d4BMMixedHorizonSturmWeight n k z *
        ((starRingEnd ℂ y) * forcing).im := by
  have hsturm := d4BMMixedHorizonHypergeometricJet_sturmDecomposition
    n k chi hz0 hz1 y dy ddy
  rw [hforcing] at hsturm
  have heq :
      (d4BMMixedHorizonSturmWeight n k z *
          d4BMMixedHorizonSturmDrift n k z : ℝ) * dy +
        (d4BMMixedHorizonSturmP n k z : ℂ) * ddy -
        (d4BMMixedHorizonSturmPotential n k chi *
          d4BMMixedHorizonSturmWeight n k z : ℝ) * y =
      (d4BMMixedHorizonSturmWeight n k z : ℂ) * forcing :=
    hsturm.symm
  have hmul := congrArg Complex.im
    (congrArg (fun v : ℂ => (starRingEnd ℂ y) * v) heq)
  simp [d4BMMixedHorizonOpticalCurrentDerivativeJet, Complex.mul_im] at hmul ⊢
  ring_nf at hmul ⊢
  linear_combination hmul

end
end RHTower
