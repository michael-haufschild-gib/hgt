# Method-model semantics audit

**Result:** `HTGeometry.SmoothMultiplicativeDichotomy` is scalar bookkeeping, not an exhaustive
classification of analytic methods. Its universal interpretations must not exclude research
directions. This audit does not supply a new method or reopen an excluded classical RH route.

## Authoritative definitions and exact limits

The entire 811-line source was inspected in ranges. `Method` has two fields: an arbitrary
`ToolFamily` label and an arbitrary rational `savingExponent`. It contains no function, exponential
sum, bound, algorithm, or proof that the assigned exponent is attained. The named examples assign
the numbers `1/6`, `4/21`, and `0`. `neither_family_suffices` compares three named records;
`no_single_family_is_joint` explicitly assumes membership in those three records. Neither quantifies
over all mathematical methods of a family.

Likewise `phaseAlgebraic := False`, `isComplete := True`, and
`scaleSeparationDiverges := True` are definitions. Theorems that unfold these flags verify their
assigned truth values; they establish no algebraicity, completion, or limiting statement about an
actual arithmetic source. `completion_barrier` compares assigned rational counts and rates.
`reciprocal_no_derivative_test` proves a particular rational exponent is zero and is not negative;
it quantifies over no derivative test. `momentOrder_diverges` proves `1 <= 1/delta` for
`0<delta<=1`, not a limit assertion. The final `muFromZeroFree` results are identities and
inequalities for a rational formula, with no analytic zero-free hypothesis in their types.

The useful verified content is the displayed rational algebra. Its interpretation as an analytic
bound needs a separate source theorem. The absence of additional axioms does not create that
missing interpretation.

## Concrete model check

The same `Method` type allows a record with label `smooth` and exponent `lindelofSaving`, and one
with label `multiplicative` and the same exponent. These records are not successful analytic
methods. They demonstrate that the type does not encode a family-wide obstruction. A scratch Lean
check verified both records and refuted the two corresponding universally quantified record
inequalities. This is a check of the model's scope, not new mathematics.

## Affected retrieval and documentation

Exact references were checked in the source, `HTGeometry.lean`, the Lindelöf campaign, the density
frontier, the Matomäki–Teräväinen–Linnik card, and the whole-corpus census. The last-but-one already
correctly calls this module exponent bookkeeping. The umbrella only imports it. The other three
documents repeated broader interpretations and were corrected at those citations.

The theorem definitions and proof terms remain unchanged. Source documentation and the incorrect
interpretations now match actual theorem scope. A comment-stripping comparison against the saved
original confirmed identical non-comment source. This is a source-trust audit within the RH
architecture search, not a proposed RH architecture.

## Validation

- `lake env lean /tmp/hgt-source-semantics-2ZzcLU/Audit.lean`: passed. Inspected theorem types,
  unfolded assigned flags, checked the counterrecords, and printed selected theorem axioms.
- `lake env lean GaloisForLFunctions/HTGeometry/SmoothMultiplicativeDichotomy.lean`: passed.
- `lake build GaloisForLFunctions.HTGeometry.SmoothMultiplicativeDichotomy`: passed; leaf target
  only, no umbrella build. Existing umbrella import remains intact.
- Selected axiom reports contain only standard Lean axioms, or none. This verifies proof trust
  without extending the statements' mathematical scope.
- `python3 scripts/formal_tools.py lint`: failed on 14 unrelated modules unreachable from their
  theorem-area umbrellas in the concurrent working tree. No error named the audited module.
  These include `EulerDeletionBalancedPeriodCurvatureNoGo`, `HedenmalmGraviAxionGapLaw`, six
  `HTGeometry.ChronologicalTensor` leaves, four `HTGeometry.Arxiv...` leaves, and two other
  `HTGeometry` leaves. No full build or edits to those modules were attempted.

No numerical experiment, new theorem, or RH implication was produced. The audit does not certify
unrelated claims elsewhere in the cited campaign documents.
