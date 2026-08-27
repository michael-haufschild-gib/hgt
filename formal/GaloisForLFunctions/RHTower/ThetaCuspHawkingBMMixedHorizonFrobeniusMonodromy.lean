import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMProjectiveCausalResponse
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTotalThirdOrderCausalCut
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalBlackHoleQNMIncidence

/-!
# Birmingham--Mokhtari mixed-horizon Frobenius monodromy

The exact mixed `+-` Birmingham--Mokhtari frequency has hypergeometric horizon parameter
`c = -N`, where `N = 2n + 2k + 2` is even. At this Frobenius collision, the coefficient
recurrence

`(j + 1)(j - N) q_(j+1) = (j + a)(j + b) q_j`

fails at `j = N`. The regular exponent-`N+1` solution contributes `(N+1) z^N` when multiplied
by `log z`. Cancellation of the recurrence obstruction therefore fixes the logarithmic coefficient

`kappa_N(a,b) = (-1)^N (a)_(N+1) (b)_(N+1) / (N! (N+1)!)`.

For real angular momentum the BM parameters satisfy `b = conj a`. Since `N` is even, `kappa` is
a strictly positive product of squared moduli. Thus the counterclockwise horizon monodromy jump is
nonzero and has strictly positive imaginary part. The second-harmonic `++` parameter is
nonresonant for nonzero real angular momentum, isolating this logarithmic horizon cut in the mixed
channel.
-/

open Complex

namespace RHTower

noncomputable section

/-- Top coefficient reached by the hypergeometric recurrence immediately before `c = -N`
collides with the regular exponent-`N+1` branch. -/
def d4HypergeometricResonantTruncationTopCoefficient
    (N : ℕ) (a b : ℂ) : ℂ :=
  (-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
    ((N.factorial : ℂ) ^ 2)

/-- Coefficient of the regular exponent-`N+1` solution times `log z` at `c = -N`. -/
def d4HypergeometricResonantFrobeniusLogCoefficient
    (N : ℕ) (a b : ℂ) : ℂ :=
  (-1 : ℂ) ^ N * (ascPochhammer ℂ (N + 1)).eval a *
      (ascPochhammer ℂ (N + 1)).eval b /
    ((N.factorial : ℂ) * ((N + 1).factorial : ℂ))

/-- Exact terminal recurrence balance: `(N+1) kappa` cancels the order-`N` Frobenius
obstruction. -/
theorem d4HypergeometricResonantFrobeniusLogCoefficient_terminalBalance
    (N : ℕ) (a b : ℂ) :
    ((N + 1 : ℕ) : ℂ) *
        d4HypergeometricResonantFrobeniusLogCoefficient N a b =
      (a + N) * (b + N) *
        d4HypergeometricResonantTruncationTopCoefficient N a b := by
  rw [d4HypergeometricResonantFrobeniusLogCoefficient,
    d4HypergeometricResonantTruncationTopCoefficient,
    ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  have hN : (N.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  field_simp

/-- The resonant logarithmic coefficient is symmetric in the two hypergeometric exponents. -/
theorem d4HypergeometricResonantFrobeniusLogCoefficient_comm
    (N : ℕ) (a b : ℂ) :
    d4HypergeometricResonantFrobeniusLogCoefficient N a b =
      d4HypergeometricResonantFrobeniusLogCoefficient N b a := by
  unfold d4HypergeometricResonantFrobeniusLogCoefficient
  ring

private theorem d4AscPochhammer_eval_conj (N : ℕ) (z : ℂ) :
    (ascPochhammer ℂ N).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((ascPochhammer ℂ N).eval z) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
      simp

/-- Even Frobenius collision order of the mixed BM horizon channel. -/
def d4BMMixedHorizonFrobeniusOrder (n k : ℕ) : ℕ :=
  2 * n + 2 * k + 2

/-- First original hypergeometric parameter at complex analytically continued BM momentum. -/
def d4BMMixedHorizonComplexA (n k : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalHypergeometricA (d4BMCausalPlusMinusFrequency n k chi) chi

/-- Second original hypergeometric parameter at complex analytically continued BM momentum. -/
def d4BMMixedHorizonComplexB (n k : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalHypergeometricB (d4BMCausalPlusMinusFrequency n k chi) chi

/-- Complex-momentum continuation of the oriented mixed-horizon logarithmic monodromy. -/
def d4BMMixedHorizonComplexMonodromyJump
    (n k : ℕ) (chi : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I) *
    d4HypergeometricResonantFrobeniusLogCoefficient
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexA n k chi)
      (d4BMMixedHorizonComplexB n k chi)

private theorem d4BMMixedHorizonComplexA_ascPochhammer_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (ascPochhammer ℂ (d4BMMixedHorizonFrobeniusOrder n k + 1)).eval
        (d4BMMixedHorizonComplexA n k chi) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro j hj hja
  have him := congrArg Complex.im hja
  rw [d4BMMixedHorizonComplexA, d4BMCausalHypergeometricA_plusMinus] at him
  simp [Complex.mul_im] at him
  exact hchi (by linarith)

private theorem d4BMMixedHorizonComplexB_ascPochhammer_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (ascPochhammer ℂ (d4BMMixedHorizonFrobeniusOrder n k + 1)).eval
        (d4BMMixedHorizonComplexB n k chi) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro j hj hjb
  have him := congrArg Complex.im hjb
  rw [d4BMMixedHorizonComplexB, d4BMCausalHypergeometricB_plusMinus] at him
  simp [Complex.mul_im] at him
  exact hchi (by linarith)

/-- Complex BM mixed-horizon monodromy is nonzero throughout `Re chi ≠ 0`. -/
theorem d4BMMixedHorizonComplexMonodromyJump_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMMixedHorizonComplexMonodromyJump n k chi ≠ 0 := by
  unfold d4BMMixedHorizonComplexMonodromyJump
    d4HypergeometricResonantFrobeniusLogCoefficient
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hfacN :
      ((d4BMMixedHorizonFrobeniusOrder n k).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (d4BMMixedHorizonFrobeniusOrder n k)
  have hfacN1 :
      ((d4BMMixedHorizonFrobeniusOrder n k + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (d4BMMixedHorizonFrobeniusOrder n k + 1)
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  · apply div_ne_zero
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (d4BMMixedHorizonComplexA_ascPochhammer_ne_zero n k chi hchi))
        (d4BMMixedHorizonComplexB_ascPochhammer_ne_zero n k chi hchi)
    · exact mul_ne_zero hfacN hfacN1

/-- Negating BM momentum exchanges the two connection exponents. -/
theorem d4BMMixedHorizonComplexA_neg
    (n k : ℕ) (chi : ℂ) :
    d4BMMixedHorizonComplexA n k (-chi) =
      d4BMMixedHorizonComplexB n k chi := by
  rw [d4BMMixedHorizonComplexA, d4BMMixedHorizonComplexB,
    d4BMCausalHypergeometricA_plusMinus, d4BMCausalHypergeometricB_plusMinus]
  ring

/-- The second connection exponent is exchanged in the opposite direction. -/
theorem d4BMMixedHorizonComplexB_neg
    (n k : ℕ) (chi : ℂ) :
    d4BMMixedHorizonComplexB n k (-chi) =
      d4BMMixedHorizonComplexA n k chi := by
  rw [d4BMMixedHorizonComplexA, d4BMMixedHorizonComplexB,
    d4BMCausalHypergeometricA_plusMinus, d4BMCausalHypergeometricB_plusMinus]
  ring

/-- Radial Frobenius monodromy is branch-shadow even. -/
theorem d4BMMixedHorizonComplexMonodromyJump_neg
    (n k : ℕ) (chi : ℂ) :
    d4BMMixedHorizonComplexMonodromyJump n k (-chi) =
      d4BMMixedHorizonComplexMonodromyJump n k chi := by
  rw [d4BMMixedHorizonComplexMonodromyJump,
    d4BMMixedHorizonComplexMonodromyJump,
    d4BMMixedHorizonComplexA_neg, d4BMMixedHorizonComplexB_neg,
    d4HypergeometricResonantFrobeniusLogCoefficient_comm]

/-- Actual analytically continued BM angular momentum carried by an Xi divisor. -/
def d4BMXiMixedHorizonAngularMomentum (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)

/-- Real momentum component is half the nonzero Xi height. -/
theorem d4BMXiMixedHorizonAngularMomentum_re
    (q : XiZeroCopy) :
    (d4BMXiMixedHorizonAngularMomentum q).re = (q.1 : ℂ).im / 2 := by
  simp [d4BMXiMixedHorizonAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    xiSpectralPoint, Complex.mul_re]

/-- Every actual Xi divisor lies in the nonvanishing complex-monodromy region. -/
theorem d4BMXiMixedHorizonAngularMomentum_re_ne_zero
    (q : XiZeroCopy) :
    (d4BMXiMixedHorizonAngularMomentum q).re ≠ 0 := by
  rw [d4BMXiMixedHorizonAngularMomentum_re]
  exact div_ne_zero (xi_divisor_support_im_ne_zero q.1) (by norm_num)

/-- Complex BM mixed-horizon monodromy evaluated on an actual Xi fibre. -/
def d4BMXiMixedHorizonComplexMonodromyJump
    (n k : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMMixedHorizonComplexMonodromyJump
    n k (d4BMXiMixedHorizonAngularMomentum q)

/-- Actual Xi-fibre mixed-horizon monodromy never vanishes. -/
theorem d4BMXiMixedHorizonComplexMonodromyJump_ne_zero
    (n k : ℕ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonComplexMonodromyJump n k q ≠ 0 := by
  exact d4BMMixedHorizonComplexMonodromyJump_ne_zero n k _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

/-- First original hypergeometric parameter of the physical real-angular-momentum mixed channel. -/
def d4BMMixedHorizonA (n k : ℕ) (chi : ℝ) : ℂ :=
  d4BMCausalHypergeometricA
    (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)

/-- Second original hypergeometric parameter of the physical real-angular-momentum mixed channel. -/
def d4BMMixedHorizonB (n k : ℕ) (chi : ℝ) : ℂ :=
  d4BMCausalHypergeometricB
    (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)

/-- The exact mixed frequency lies at the negative-integral horizon parameter `-N`. -/
theorem d4BMMixedHorizonRadialC_eq_neg_frobeniusOrder
    (n k : ℕ) (chi : ℝ) :
    d4BMCausalRadialC
        (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) =
      -(d4BMMixedHorizonFrobeniusOrder n k : ℂ) := by
  rw [d4BMCausalRadialC_plusMinus_eq_negNat]
  simp [d4BMMixedHorizonFrobeniusOrder]

/-- The mixed-channel Frobenius collision has even order. -/
theorem d4BMMixedHorizonFrobeniusOrder_negOne_pow
    (n k : ℕ) :
    (-1 : ℂ) ^ d4BMMixedHorizonFrobeniusOrder n k = 1 := by
  simp [d4BMMixedHorizonFrobeniusOrder, pow_add]

/-- Physical BM mixed connection parameters are conjugates. -/
theorem d4BMMixedHorizonB_eq_conj_A
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonB n k chi =
      starRingEnd ℂ (d4BMMixedHorizonA n k chi) := by
  rw [d4BMMixedHorizonA, d4BMMixedHorizonB,
    d4BMCausalHypergeometricA_plusMinus, d4BMCausalHypergeometricB_plusMinus]
  norm_num [map_sub, map_add, map_neg, map_div₀, map_mul, map_ofNat,
    Complex.conj_I]
  ring

/-- Positive real weight underlying the mixed-channel logarithmic coefficient. -/
def d4BMMixedHorizonFrobeniusWeight (n k : ℕ) (chi : ℝ) : ℝ :=
  Complex.normSq
      ((ascPochhammer ℂ (d4BMMixedHorizonFrobeniusOrder n k + 1)).eval
        (d4BMMixedHorizonA n k chi)) /
    ((d4BMMixedHorizonFrobeniusOrder n k).factorial *
      (d4BMMixedHorizonFrobeniusOrder n k + 1).factorial : ℕ)

/-- At the BM collision the complex logarithmic coefficient is exactly the real Frobenius
weight. -/
theorem d4BMMixedHorizonFrobeniusLogCoefficient_eq_weight
    (n k : ℕ) (chi : ℝ) :
    d4HypergeometricResonantFrobeniusLogCoefficient
        (d4BMMixedHorizonFrobeniusOrder n k)
        (d4BMMixedHorizonA n k chi) (d4BMMixedHorizonB n k chi) =
      (d4BMMixedHorizonFrobeniusWeight n k chi : ℂ) := by
  rw [d4HypergeometricResonantFrobeniusLogCoefficient,
    d4BMMixedHorizonB_eq_conj_A,
    d4BMMixedHorizonFrobeniusOrder_negOne_pow, one_mul,
    d4AscPochhammer_eval_conj, Complex.mul_conj]
  simp [d4BMMixedHorizonFrobeniusWeight]

private theorem d4BMMixedHorizonAscPochhammer_ne_zero
    (n k : ℕ) (chi : ℝ) :
    (ascPochhammer ℂ (d4BMMixedHorizonFrobeniusOrder n k + 1)).eval
        (d4BMMixedHorizonA n k chi) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro j hj hja
  have hre := congrArg Complex.re hja
  rw [d4BMMixedHorizonA, d4BMCausalHypergeometricA_plusMinus] at hre
  norm_num at hre
  have hfour : (4 : ℝ) * (j : ℝ) =
      4 * (n : ℝ) + 4 * (k : ℝ) + 5 := by
    linarith
  have hcast : (4 : ℤ) * (j : ℤ) =
      4 * (n : ℤ) + 4 * (k : ℤ) + 5 := by
    exact_mod_cast hfour
  omega

/-- The physical BM logarithmic horizon coefficient is strictly positive for every real `chi`. -/
theorem d4BMMixedHorizonFrobeniusWeight_pos
    (n k : ℕ) (chi : ℝ) :
    0 < d4BMMixedHorizonFrobeniusWeight n k chi := by
  rw [d4BMMixedHorizonFrobeniusWeight]
  apply div_pos
  · exact Complex.normSq_pos.mpr
      (d4BMMixedHorizonAscPochhammer_ne_zero n k chi)
  · positivity

/-- Counterclockwise `log z` monodromy of the resonant mixed horizon branch. -/
def d4BMMixedHorizonCounterclockwiseMonodromyJump
    (n k : ℕ) (chi : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I) *
    d4HypergeometricResonantFrobeniusLogCoefficient
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonA n k chi) (d4BMMixedHorizonB n k chi)

/-- The mixed BM horizon monodromy is `i` times a strictly positive real weight. -/
theorem d4BMMixedHorizonCounterclockwiseMonodromyJump_eq
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi =
      Complex.I *
        ((2 * Real.pi * d4BMMixedHorizonFrobeniusWeight n k chi : ℝ) : ℂ) := by
  rw [d4BMMixedHorizonCounterclockwiseMonodromyJump,
    d4BMMixedHorizonFrobeniusLogCoefficient_eq_weight]
  push_cast
  ring

/-- The oriented BM mixed-horizon monodromy has strictly positive imaginary part. -/
theorem d4BMMixedHorizonCounterclockwiseMonodromyJump_im_pos
    (n k : ℕ) (chi : ℝ) :
    0 < (d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi).im := by
  rw [d4BMMixedHorizonCounterclockwiseMonodromyJump_eq]
  simp
  exact mul_pos (by positivity) (d4BMMixedHorizonFrobeniusWeight_pos n k chi)

/-- The mixed BM logarithmic horizon cut never disappears. -/
theorem d4BMMixedHorizonCounterclockwiseMonodromyJump_ne_zero
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact (ne_of_gt
    (d4BMMixedHorizonCounterclockwiseMonodromyJump_im_pos n k chi)) him

/-- Exact horizon parameter of the second-harmonic BM response. -/
theorem d4BMCausalRadialC_plusPlus_real
    (n : ℕ) (chi : ℝ) :
    d4BMCausalRadialC
        (d4BMCausalPlusPlusFrequency n (chi : ℂ)) =
      -(4 * (n : ℂ) + 2) - 2 * Complex.I * (chi : ℂ) := by
  simp [d4BMCausalRadialC, d4BMCausalPlusPlusFrequency,
    d4BMCausalQNMPlus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Nonzero real angular momentum excludes every integral Frobenius collision in the `++`
channel. -/
theorem d4BMCausalRadialC_plusPlus_ne_negNat_of_ne_zero
    (n j : ℕ) (chi : ℝ) (hchi : chi ≠ 0) :
    d4BMCausalRadialC
        (d4BMCausalPlusPlusFrequency n (chi : ℂ)) ≠ -(j : ℂ) := by
  rw [d4BMCausalRadialC_plusPlus_real]
  intro h
  have him := congrArg Complex.im h
  norm_num at him
  exact hchi (by linarith)

/-- If the actual mixed response jump is the BM logarithmic monodromy and the nonresonant `++`
response has no jump, the complete nonlinear causal source is a single contact-free horizon
channel. -/
theorem d4BMMixedHorizonMonodromy_totalCausalCut
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    (n k : ℕ) (chi : ℝ)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C RppRet RpmRet RppAdv RpmAdv p m =
      d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi • B p u := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    hpm, hpp]
  simp

/-- Cokernel form of the mixed BM horizon-monodromy incidence law. -/
theorem d4BMMixedHorizonMonodromy_totalCokernelCausalCut
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    (n k : ℕ) (chi : ℝ)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m =
      d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi * ell (B p u) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut,
    d4BMMixedHorizonMonodromy_totalCausalCut
      B C RppRet RpmRet RppAdv RpmAdv p m u n k chi hpm hpp]
  exact map_smul ell (d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi) (B p u)

end

end RHTower
