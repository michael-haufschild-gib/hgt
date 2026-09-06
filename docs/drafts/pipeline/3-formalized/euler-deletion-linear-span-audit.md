# Exact classical dictionary for deletion prefixes

**Stage:** 3-formalized. **RH implication:** none. **Novelty verdict:** the
proposed linear completion identifies a published classical family.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionLinearSpanAudit.lean`.
Namespace: `RHTower.DeletionLinearSpanAudit`.

`prefixVector` is defined from the existing literal integer-coefficient sum.
`fractionVector` is independently defined as the complex-valued sequence
`fract(N/(q+1))`. `prefixVector_eq_mul_fraction` proves equality after multiplication
by `q+1`. `finiteCombination_eq` gives the explicit coefficient change for every
finite combination. `span_prefixVector_eq_fractionVector` proves both span
inclusions, and `closure_span_eq` applies in any chosen topology on the whole
sequence carrier. `tail_cell_eq_bdGenFun` identifies the normalized prefix with
the actual existing Báez-Duarte generator on every open integer cell.

The premise-free `literal_prefix_classical_linear_dictionary` packages the exact
source identity and equality of spans. It has no density, zero, or RH premise.

`lake env lean /tmp/hgt-deletion-linear-audit-9rjQNq/Audit.lean` passed six axiom
audits, covering the source dictionary, finite combinations, span, closure, cell
identity, and capstone. Dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. Production matches the audited scratch body. Narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionLinearSpanAudit` passed;
umbrella import is wired. No full or umbrella build ran. Repository-wide
`scripts/formal_tools.py lint` failed solely on concurrent work outside this module:
`RHTower/ThetaTiltLogDensity.lean` was unreachable from its theorem-area umbrella.
No lint error named this audit module. Output:
`/tmp/hgt-deletion-linear-audit-9rjQNq/lint.log`. The earlier compatible-curvature
audit passed global lint, but this latest repository-wide check did not.
No mathematical computation or external proof certificate was used.

The [paper and literature audit](../2-fully-proven/euler-deletion-linear-span-audit.md)
states the precise limits. This proves an identification with classical
mathematics, not a new RH mechanism. No new positive architectural salvage was
found in the linear completion. Higher chronological operations remain a separate
unfulfilled research obligation.
