# Composed-failure support-orbit and Walsh-genesis law — formalized core

- **ID:** ULF-EAG-2-CORE
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveComposedFailureGenesis`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED CORE] [NO ROUTE PREMISE] [NOT RH]

## Certified mechanism

For every finite failure-coordinate type and every finite deterministic reporter transporting
elementary flips and detecting each active flip in every context, Lean proves:

1. equal outputs have equal active supports;
2. the attained output type has cardinal at least `2^(n+1)-1`;
3. the canonical support/parity reporter is legal and attains that bound exactly;
4. its fibres are exactly equal-support/equal-parity classes;
5. mixed channels across two independent blocks have cardinal
   `(2^|A|-1)(2^|B|-1)`.

The arbitrary-minimal-reporter rigidity classification and general convex `2n`-atom repair remain
paper-only.  They are not included in this formalized-core status.

## Headline declarations

- `ComposedFailureReporter.support_eq_of_q_eq`
- `composedFailureReporter_card_lower_bound_closed`
- `composedFailureCanonicalQ_eq_iff_closed`
- `composedFailureCanonicalReporter_card_exact_closed`
- `card_composedFailureMixedChannels_closed`
- `composedFailureGenesisMechanism_closed`

## Audit

- direct module elaboration: green
- umbrella wiring: complete
- project lint: `scripts/formal_tools.py lint --check-generated` passed
- umbrella build: `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed
  (`11,476` jobs); replay warnings came from pre-existing modules, while the new module built cleanly
- axiom print: every headline declaration depends only on `propext`, `Classical.choice`, and
  `Quot.sound`
