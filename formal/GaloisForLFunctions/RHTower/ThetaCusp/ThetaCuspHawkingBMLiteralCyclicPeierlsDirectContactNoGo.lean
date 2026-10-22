import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsSameRateNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsClockDichotomyNoGo

/-!
# Direct clock-matched cyclic Peierls contact no-go

An atomic literal two-source CTP pairing can meet the clock of a one-branch
B2 metric contact only when its two source branches agree.  Its native
pairing, full-circle pairing, and explicit full-minus-native lift then all
vanish.  Consequently no direct, clock-preserving scalar source pairing can
realize the B2 contact.

The surviving literal source is the complementary-rate channel, whose clock
is `-6`; it must therefore be transported by a genuinely metric-valued,
clock-changing carrier rather than identified directly with the one-branch
contact.

Proof-chain role:
`literal two-event CTP atoms -> clock-matched classification -> all direct
scalar contact components vanish -> retire direct B2 Peierls-to-contact
identification; retain cross-branch metric carrier`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsDirectContactNoGo

open D4BMCuspProjection
open D4BMFullSourceReciprocity D4BMFullAngularCausalPeierls
open D4BMLiteralCyclicPeierlsSameRateNoGo
open D4BMLiteralCyclicPeierlsClockDichotomyNoGo
open D4BMLiteralCyclicPeierlsLiftDefect

noncomputable section
set_option autoImplicit false

/-- A literal two-source atom at the clock of a one-branch B2 contact has
equal source branches.  The alternative complementary pair has clock `-6`,
which cannot equal the one-branch contact clock at an actual Xi zero. -/
theorem clockMatched_branches_eq (q : XiZeroCopy) (branch b c : Bool)
    (hclock : physicalRate q b + physicalRate q c = 2 * physicalRate q branch) :
    b = c := by
  cases b <;> cases c
  · rfl
  · exfalso
    apply oneBranch_contact_clock_ne_complementary q branch
    calc
      2 * physicalRate q branch = physicalRate q false + physicalRate q true := hclock.symm
      _ = physicalRate q true + physicalRate q false := by ring
  · exfalso
    apply oneBranch_contact_clock_ne_complementary q branch
    exact hclock.symm
  · rfl

/-- Complete direct-contact obstruction.  Once a literal CTP atom is forced
to carry the B2 one-branch clock, every scalar source component available to
the direct identification is zero: native, lifted, and full-circle. -/
theorem direct_clockMatched_components_zero (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ)
    (hclock : physicalRate q b + physicalRate q c = 2 * physicalRate q branch) :
    causalSourcePair q b c a d X k = 0 ∧
      causalSourceLiftDefect q branch b c a d X k = 0 ∧
      fullCausalSourcePair q branch b c a d X k = 0 := by
  have hbc := clockMatched_branches_eq q branch b c hclock
  subst c
  exact ⟨causalSourcePair_same_rate_zero q b a d X k,
    causalSourceLiftDefect_same_rate_zero q branch b a d X k,
    fullCausalSourcePair_same_rate_zero q branch b a d X k⟩

/-- In particular, a nonzero literal full-circle CTP scalar pairing cannot
be directly clock-matched to a one-branch B2 contact. -/
theorem fullCausalSourcePair_ne_zero_clock_mismatch (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ)
    (hnonzero : fullCausalSourcePair q branch b c a d X k ≠ 0) :
    physicalRate q b + physicalRate q c ≠ 2 * physicalRate q branch := by
  intro hclock
  exact hnonzero (direct_clockMatched_components_zero q branch b c a d X k hclock).2.2

end

end RHTower.D4BMLiteralCyclicPeierlsDirectContactNoGo
