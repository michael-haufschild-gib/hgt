# Cyclic source with a possibly vanishing landing scalar

- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** THEOREM (Lean), auxiliary classification; proposed RH substitution rejected
- **RH status:** no new zero-forced relation or off-line exclusion.
- **Novelty status:** elementary module presentation; no claim of new scientific knowledge.

## Proposed use and admission failure

The corpus's `DerivedSelectionGeometry/SourceOrientation` has a cyclic source with invariant,
surjective trace `eps`, landing `(c eps(x),0)`, and rotation `(x,y) -> (y,q x)`.
Its orientation quotient is `R/(q-1)` when both q and c are units. A possible RH use would
put a zeta-dependent response into c and try to constrain q at a zero. That use loses the unit
hypothesis precisely at the point where it needs the theorem.

The original unit-scalar theorem is correct. The classification below settles the proposed
substitution without assuming either scalar is a unit.

## Closed statement and proof

For arbitrary q,c in any commutative ring R, the source boundary with identity source and trace is

    B = R(-c,cq) + R(cq,-cq).

The same boundary holds for every invariant surjective trace, without any unit assumption on c.
The invertible change of coordinates `(x,y) -> (-x,y+qx)` takes the two generators to
`(c,0)` and `(-cq,cq(q-1))`. Adding q times the first generator to the second gives
`(0,cq(q-1))`. Hence

    (R x R)/B  ~=  R/(c) x R/(cq(q-1)).

No division by c or q, domain assumption, or principal-ideal-domain hypothesis is needed.
Its annihilator is exactly `(cq(q-1))`, since that ideal is contained in `(c)`.
In particular c=0 gives the full free module R x R, independently of q. Over a field, c nonzero
and q outside {0,1} gives the zero module; q=0 or q=1 with c nonzero gives one free coordinate.
The previously proved orientation quotient is the unit-q, unit-c case of this decomposition.

## No-go closure

- **Failure:** substituting c=zeta(s) into the unit-c theorem cannot select q at a zeta zero.
  The literal zero-source quotient retains both coordinates for every q.
- **Positive survivor:** the full arbitrary-scalar quotient and annihilator classification above.
- **Scope:** this tests this literal cyclic-source construction. It does not impose a universal
  restriction on all uses of homology, quotients, or source deformations in an RH proof.
- **Paper status:** elementary coordinate proof given above.
- **Lean status:** closed in `SourceScalarBoundary.lean`, namespace
  `GaloisForLFunctions.HTGeometry.DerivedSelection.NonunitSource`.
  `quotientEquiv` and `annihilator` give the full commutative-ring classification;
  `generalQuotientEquiv` and `general_annihilator` extend it to every invariant surjective
  trace. `field_finrank_classification` states the entire field-valued case split:
  dimension 2 if c=0, dimension 1 if c is nonzero and q is 0 or 1, and dimension 0 otherwise.
  These are universally quantified algebraic theorems, with no unproved RH premise.

## Current source evidence

Searches `source annihilator`, `source nonunit`, `cyclic singular`, and `nonunit` filtered to
`DerivedSelection` were paired with `rg` and direct proof inspection of `SourceOrientation`
and `TwoPathIncompatibility`. The existing `srcIncompatEquiv` and
`annihilator_srcIncompatModule` require both `IsUnit q` and `IsUnit c`. The two-path module
already retains c in its individual range formulas before specializing to unit c.
Search misses are not a novelty certificate. No mathematical experiment is required.

## Verification

- Scratch proof and direct source check with `lake env lean <file>` passed.
- Scratch axiom audit of all 20 public declarations (14 theorems, four definitions, two
  abbreviations) contains only `propext`, `Classical.choice`, and `Quot.sound`.
  No added postulate or computational certificate was used.
- Final foreground build with one Lean worker passed:
  `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceScalarBoundary`.
  Only the new leaf was built; the reported 8658 jobs include cached dependencies.
- The leaf is wired into `formal/GaloisForLFunctions/HTGeometry.lean`.
  No full or umbrella build was run.
- Scratch proofs, name checks, and axiom output: `/tmp/hgt-source-scalar-wZKpfR`.
- `python3 scripts/formal_tools.py index` refreshed the formal indexes. The research query
  `field_finrank_classification` filtered to `SourceScalarBoundary` retrieves the capstone.
- `python3 scripts/formal_tools.py lint` passed, with existing large-file warnings.
  Every Lean process started for this classification finished; no owned worker remains.
