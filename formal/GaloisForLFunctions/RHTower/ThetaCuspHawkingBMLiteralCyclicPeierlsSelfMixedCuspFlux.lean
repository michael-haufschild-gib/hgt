import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedParticularCuspFlux
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence

/-!
# Self-copy lower Weyl coefficient of the literal mixed cusp flux

For a left-half Xi copy, the lower square/reader Weyl channel of the actual
mixed particular cusp flux is nonzero on either physical source branch.  This
is the source-side input for a growth-based B2 no-go: the cap/contact boundary
would have to remove a literal nonzero growing channel, rather than merely a
scalar proxy.

Proof-chain role:
`off-line Xi copy -> reflected left copy -> nonzero lower mixed cusp flux
coefficient -> physical B2 boundary transport or literal cyclic-Peierls
obstruction -> shared RBH/PW-B/FZZ-P current -> RH`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsSelfMixedCuspFlux

open D4BMCuspProjection D4BMModularCore D4BMGlobalAngularResponse
open D4BMMixedParticularCuspFlux
open D4BMLiteralCyclicPeierlsAffineCuspIncidence

noncomputable section
set_option autoImplicit false

private theorem physicalRate_add_real_ne_zero (q : XiZeroCopy) (branch : Bool)
    (c : ℝ) : D4BMCuspProjection.physicalRate q branch + (c : ℂ) ≠ 0 := by
  intro h
  apply xi_divisor_support_im_ne_zero q.1
  have him := congrArg Complex.im h
  cases branch <;>
    norm_num [D4BMCuspProjection.physicalRate, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.sub_im, Complex.neg_im] at him ⊢ <;>
    linarith

private theorem parameter_ne_zero (q : XiZeroCopy) (branch : Bool) :
    parameter q branch ≠ 0 := by
  rw [physicalRate_parameter]
  exact mul_ne_zero (physicalRate_add_real_ne_zero q branch 1)
    (physicalRate_add_real_ne_zero q branch 2)

private theorem lower_source_coefficient_ne_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    sourceCoefficient q 2 ≠ 0 := by
  have hLambda : reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ≠ 0 := by
    intro h
    exact affine_lower_lambda_zero_not_left q ⟨h, hleft⟩
  have hweyl : weylCoefficient q false =
      reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) := by
    unfold weylCoefficient D4BMGlobalAngularResponse.center
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,
      Bool.false_eq_true, if_false]
    congr 1
    ring
  simp only [sourceCoefficient, Matrix.cons_val_two]
  rw [hweyl]
  exact pow_ne_zero 2 hLambda

private theorem lower_source_power_ne_zero (q : XiZeroCopy) :
    sourcePower q 2 ≠ 0 := by
  change 2 - 2 * (q.1 : ℂ) ≠ 0
  intro h
  apply xi_divisor_support_im_ne_zero q.1
  have him := congrArg Complex.im h
  norm_num [Complex.sub_im, Complex.mul_im, Complex.mul_re] at him ⊢
  linarith

private theorem lower_reader_source_gap_ne_zero (q : XiZeroCopy) :
    readerPower q - sourcePower q 2 ≠ 0 := by
  change (1 - (q.1 : ℂ) / 2) - (2 - 2 * (q.1 : ℂ)) ≠ 0
  intro h
  apply xi_divisor_support_im_ne_zero q.1
  have him := congrArg Complex.im h
  norm_num [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.div_im] at him ⊢
  linarith

/-- At every left-half self-copy, the lower Weyl coefficient of the literal
actual mixed cusp flux is nonzero on each physical source branch. -/
theorem fluxCoefficient_self_lower_ne_zero (q : XiZeroCopy) (branch : Bool)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    fluxCoefficient q q branch 2 ≠ 0 := by
  unfold fluxCoefficient
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (div_ne_zero (parameter_ne_zero q branch) (by norm_num))
              (lower_source_coefficient_ne_zero q hleft))
            (reader_completion_ne_zero q))
          (lower_source_power_ne_zero q))
        (reader_power_ne_zero q))
      (lower_reader_source_gap_ne_zero q))
    (denominator_ne_zero q branch 2)

end
end RHTower.D4BMLiteralCyclicPeierlsSelfMixedCuspFlux
