import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# Clock dichotomy for literal cyclic Peierls source pairs

The complementary physical source rates have a fixed total clock `-6`, while
a one-branch B2 contact carries clock `2 * physicalRate q branch`.  At an
actual Xi zero these clocks cannot agree.  Together with the same-rate Peierls
vanishing, this is the exact clock obstruction faced by a literal B2 source to
same-branch-contact realization.

Proof-chain role:
`same-rate Peierls vanishing OR complementary-rate clock -6` versus
`one-branch B2 contact clock 2s` -> eliminate every clock-preserving direct
scalar-Peierls-to-contact identification -> HB B2 no-go or new nonliteral
carrier`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsClockDichotomyNoGo

open D4BMCuspProjection

noncomputable section
set_option autoImplicit false

/-- The two opposite literal source rates have an exact, parameter-independent
sum. -/
theorem complementary_physicalRate_sum (q : XiZeroCopy) :
    physicalRate q true + physicalRate q false = (-6 : ℂ) := by
  simp only [physicalRate, if_true, Bool.false_eq_true, if_false]
  ring

/-- No actual Xi zero can make the complementary-source clock equal the clock
of a one-branch quadratic B2 contact. -/
theorem oneBranch_contact_clock_ne_complementary (q : XiZeroCopy)
    (branch : Bool) :
    2 * physicalRate q branch ≠ physicalRate q true + physicalRate q false := by
  intro h
  have hhalf : (q.1 : ℂ) = 1 / 2 := by
    cases branch
    · simp only [physicalRate, Bool.false_eq_true, if_false, if_true] at h ⊢
      linear_combination (-1 / 4 : ℂ) * h
    · simp only [physicalRate, if_true, Bool.false_eq_true, if_false] at h ⊢
      linear_combination (1 / 4 : ℂ) * h
  have him : (q.1 : ℂ).im = 0 := by
    have hi := congrArg Complex.im hhalf
    norm_num at hi ⊢
    exact hi
  exact xi_divisor_support_im_ne_zero q.1 him

/-- Equivalently, a clock-preserving identification of an opposite-rate
source pair with the B2 one-branch contact is impossible at every actual Xi
zero. -/
theorem no_clock_preserving_complementary_contact (q : XiZeroCopy)
    (branch : Bool) :
    2 * physicalRate q branch ≠ (-6 : ℂ) := by
  rw [← complementary_physicalRate_sum]
  exact oneBranch_contact_clock_ne_complementary q branch

end

end RHTower.D4BMLiteralCyclicPeierlsClockDichotomyNoGo
