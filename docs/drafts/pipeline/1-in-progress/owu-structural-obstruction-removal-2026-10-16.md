# OWU: structural obstruction removal

Status: IN PROGRESS. No claimed frontier advance.

## Objective and constraints

Prove one structural result removing a hard OWU obstruction. No improved bound,
new RH equivalence, conditional receiver, numerical experiment, external search,
or external novelty audit. Use the Lean corpus as mathematical evidence. Preserve
pre-existing workspace edits. Final proofs must introduce no unproved premises,
new axioms, computation certificates, or heartbeat increases.

## Plan

1. Inspect OWU's current Lean frontier and search the entire indexed corpus.
2. Form and attack competing structural conjectures; record failures and pivots.
3. Complete a dependency-closed mathematical proof before formalization.
4. Verify new declarations in Lean, wire leaf modules into RHTower, audit axioms,
   run formal lint, and remove owned scratch artifacts. No umbrella/full builds.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session.
Independent tool reads use awaited parallel calls. Serena ignores Lean paths;
the attempted symbol lookup failed, so Lean inspection uses `rg` and bounded reads.

## Verified starting point

- `OddWeilSpectralMeasure`: odd positivity produces a positive Nevanlinna measure
  on critical ordinates and the real cut; the central constant is invisible to
  odd tests. The converse is also proved.
- `WeilCutEvenMeanZeroDeficit`: even mean-zero positivity is equivalent to cut
  removal for an odd-positive weight. This does not produce that positivity.
- `WeilDilationRayCriterion`: the single dilation ray would remove both cut mass
  and the central obstruction, but its all-scale positivity remains an input.
- `OddSectorPoleDensityLaw`: positive pole weight requires nonzero Abel density.
  Tempered pole-free weights cannot supply a positive-pole source.
- `WeilConeUniquenessUnconditional`, `EvenSectorTwistedArcNull`: arithmetic
  blindness of a shifted-Gamma family supplies an independent null identity.
  Its existing parity does not directly exploit odd positivity.

## Conjecture loop

1. Repeated odd spectral tests alone remove the cut: REJECTED. The exact spectral
   weights are nonnegative on the cut. Need arithmetic structure beyond this
   representation.
2. Differentiate the existing blind null family to get an odd blind family:
   UNPROVED. Blindness at log-integer nodes does not imply blindness of the
   second derivative there. This missing cancellation cannot be assumed.
3. Arithmetic rigidity removes the central obstruction once the cut is absent:
   UNDER INVESTIGATION. Investigate the mean-zero positive cone and its null
   families, without treating central nonnegativity as an extra premise.

## Search coverage

Initial whole-corpus hybrid and deep searches reported indexed source coverage,
but older coverage snapshots and unavailable semantic coverage. Deep results
were partial. Candidate applicability is checked against actual Lean sources;
absence from search is not treated as proof of absence.
