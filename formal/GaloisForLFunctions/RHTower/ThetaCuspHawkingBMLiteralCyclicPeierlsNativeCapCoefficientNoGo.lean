import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# Native-cap coefficient rigidity for literal cyclic Peierls action

The physical two-leg cap action differs from its full-minus-native lift defect
by `c(s) Q`, where `c(s) = 1 - s (s - 1) / 4`.  This file proves that the
coefficient cannot disappear on either physical Xi branch.  Hence a literal
metric/current realization must retain the native cap action (or prove that
action itself vanishes); it cannot identify the metric cap action with the
lift defect by coefficient cancellation.

Proof-chain role:
`literal metric cap = lift defect + c(s) native cap`, `c(s) ≠ 0`
`-> retain native cap action -> complete two-leg metric/current comparison`
`-> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsNativeCapCoefficientNoGo

open D4BMCuspProjection

noncomputable section
set_option autoImplicit false

/-- The forced native-cap coefficient in the literal metric action is nonzero
on every actual Xi mode and either physical branch. -/
theorem native_cap_coefficient_ne_zero (q : XiZeroCopy) (branch : Bool) :
    (1 : ℂ) - physicalRate q branch * (physicalRate q branch - 1) / 4 ≠ 0 := by
  intro h
  have hmul : physicalRate q branch * (physicalRate q branch - 1) = (4 : ℂ) := by
    linear_combination -4 * h
  have him : (physicalRate q branch).re * (physicalRate q branch).im +
      (physicalRate q branch).im * ((physicalRate q branch).re - 1) = 0 := by
    have hi := congrArg Complex.im hmul
    simpa [Complex.mul_im] using hi
  have hfactor : (2 * (physicalRate q branch).re - 1) *
      (physicalRate q branch).im = 0 := by
    linarith
  have hleft : 2 * (physicalRate q branch).re - 1 ≠ 0 := by
    intro hz
    have hr := (physicalRate_re_bounds q branch).2
    linarith
  have hz : (physicalRate q branch).im = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hleft
  apply xi_divisor_support_im_ne_zero q.1
  cases branch <;>
    norm_num [physicalRate, Complex.mul_im, Complex.sub_im, Complex.neg_im] at hz
  · exact hz
  · exact hz

end

end RHTower.D4BMLiteralCyclicPeierlsNativeCapCoefficientNoGo
