import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent

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

open D4BMModularCore

noncomputable section
set_option autoImplicit false

/-- The forced native-cap coefficient in the literal metric action is nonzero
on every actual Xi mode and either physical branch. -/
theorem native_cap_coefficient_ne_zero (q : XiZeroCopy) (branch : Bool) :
    (1 : ℂ) - physicalRate q branch * (physicalRate q branch - 1) / 4 ≠ 0 := by
  intro h
  have hmul : physicalRate q branch * (physicalRate q branch - 1) = (4 : ℂ) := by
    linear_combination -4 * h
  have him : (2 * (physicalRate q branch).re - 1) *
      (physicalRate q branch).im = 0 := by
    have hi := congrArg Complex.im hmul
    norm_num [Complex.mul_im, Complex.sub_re, Complex.sub_im] at hi
    linarith
  have hleft : 2 * (physicalRate q branch).re - 1 ≠ 0 := by
    have hl := (xi_divisor_support_re_mem_open_unit q.1).1
    have hr := (xi_divisor_support_re_mem_open_unit q.1).2
    cases branch <;>
      norm_num [physicalRate, Complex.sub_re, Complex.neg_re] <;>
      intro hz <;> linarith
  have hz : (physicalRate q branch).im = 0 :=
    (mul_eq_zero.mp him).resolve_left hleft
  apply xi_divisor_support_im_ne_zero q.1
  cases branch <;> simpa [physicalRate] using hz

end

end RHTower.D4BMLiteralCyclicPeierlsNativeCapCoefficientNoGo
