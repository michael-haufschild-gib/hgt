import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsLiftDefect

/-!
# Diagonal obstruction for the literal cyclic Peierls lift defect

The full-minus-native lift defect is an antisymmetrized two-source Peierls
pairing.  It therefore vanishes on an identical pair of source legs.  The
same-branch metric contact is quadratic and is not such a diagonal Peierls
pairing.  Consequently a B2 realization must remain polarized until a
separate source-to-metric-current boundary intertwiner is constructed.

Proof-chain role:
`literal lift defect -> diagonal self-pairing obstruction -> polarized
source-to-metric-current intertwiner -> same-branch contact boundary -> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsDiagonalLiftNoGo

open D4BMFullAngularCausalPeierls D4BMFullSourceReciprocity
open D4BMLiteralCyclicPeierlsLiftDefect

noncomputable section
set_option autoImplicit false

/-- The antisymmetrized full-minus-native lift defect is identically zero on
two identical source legs.  Thus it cannot itself be the nontrivial diagonal
same-branch metric contact; only a polarized boundary-current construction can
remain as the B2 contact candidate. -/
theorem causalSourceLiftDefect_self (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) :
    causalSourceLiftDefect q branch b b a a X k = 0 := by
  have h := fullCausalSourcePair_eq_native_add_liftDefect q branch b b a a X k
  rw [fullCausalSourcePair_self, causalSourcePair_self, zero_add] at h
  exact h.symm

end

end RHTower.D4BMLiteralCyclicPeierlsDiagonalLiftNoGo
