import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalLiftHorizonCurrent

/-!
# Ordered physical current for the literal cyclic Peierls seam

The full two-event causal source pairing is exactly skew when its two source
legs are exchanged.  This leaf proves the matching fact for the only possible
physical boundary target: the original Einstein current with its literal
master-source contact, and the contact-completed angular current.  Hence an
ordered cap-to-current transgression is algebraically compatible with the
causal functional; a scalar or symmetrized boundary functional is not.

This does not identify either current with the noncompact full-circle causal
pairing.  That remaining equality must transport the explicit lift defect.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsOrderedCurrent

open GaloisForLFunctions.HTGeometry D4BMHorizon D4BMPhysicalLiftCurrent
noncomputable section
set_option autoImplicit false

/-- The literal master-source contact is itself ordered: exchanging its two
source legs reverses every physical face. -/
theorem liftContact_ctp_swap (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ)
    (z : D4BMHorizon.Point) :
    liftContact q s t a b r v z = -liftContact q t s b a r v z := by
  ext j
  fin_cases j <;> simp [liftContact, liftMaster] <;> ring

/-- After retaining that contact, the complete angular master current has the
same CTP exchange law as the literal retarded-minus-advanced source pairing. -/
theorem liftAngularCurrent_ctp_swap (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ)
    (z : D4BMHorizon.Point) :
    liftAngularCurrent q s t a b r v z =
      -liftAngularCurrent q t s b a r v z := by
  ext j
  fin_cases j <;> simp [liftAngularCurrent] <;> ring

/-- The uncompleted Einstein action current is consequently ordered as well;
this derives from the exact current-plus-contact decomposition rather than
discarding the contact. -/
theorem liftCurrent_ctp_swap (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ)
    (z : D4BMHorizon.Point) :
    liftCurrent q s t a b r v z = -liftCurrent q t s b a r v z := by
  have hst := lift_current_add_contact q s t a b r v z
  have hts := lift_current_add_contact q t s b a r v z
  rw [eq_sub_of_add_eq hst, liftAngularCurrent_ctp_swap, liftContact_ctp_swap]
  rw [eq_sub_of_add_eq hts]
  ring

end
end RHTower.D4BMLiteralCyclicPeierlsOrderedCurrent
