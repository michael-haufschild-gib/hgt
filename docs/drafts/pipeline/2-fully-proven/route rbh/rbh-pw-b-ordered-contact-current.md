# RBH / PW-B ordered contact-current compatibility

- **ID:** RBH-PW-B-OCC
- **Stage:** 2-fully-proven
- **Role:** necessary CTP-seam premise

For arbitrary two source legs `(s,a)` and `(t,b)`, the literal source-contact
current and its completed angular current obey

`C(s,a;t,b) = -C(t,b;s,a)`,

face by face. The uncompleted Einstein current has the same law, derived from
the exact identity

`EinsteinCurrent + SourceContact = AngularCurrent`.

This is not a convention: all radial, onset, angular, and contact terms occur
in the displayed Lean definitions. It establishes compatibility with the exact
skew law of `fullCausalSourcePair`; any scalar/symmetrized cap target cannot be
the literal CTP seam.

## Whole-route consequence

The boundary target for PW-B's complementary B2 carrier is necessarily the
ordered contact-completed angular current. The remaining theorem must equate
the full noncompact source action to that target while transporting the explicit
full-minus-native lift defect. This result neither proves that transgression nor
retires PW-B.

## Lean status

`ThetaCuspHawkingBMLiteralCyclicPeierlsOrderedCurrent.lean` is source-audited
with `lake env lean`; wired to `RHTower.lean`. No umbrella build was run.
