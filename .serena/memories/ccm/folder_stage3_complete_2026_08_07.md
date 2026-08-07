# ccm folder: stage 2 emptied, all three cards promoted (2026-08-07)

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/ccm/` no longer exists.  Its three
cards were already fully formalized in committed Lean; the residual work was audit + promotion.

Promoted to `3-formalized/new_scientific_knowledge/ccm/`, each with a `-formalized.md` certificate:

| card | module |
|---|---|
| `fixed-trace-ideal-gamma-cofinal-normalizer-law` | `RHTower/PrimeFirstTraceGammaCofinalNormalizerFrontier.lean` (18 decls) |
| `cofinal-gamma-bockstein-determinant-transgression` | `RHTower/PrimeGammaCofinalBocksteinDeterminantTransgression.lean` (9 decls) |
| `cofinal-gamma-bockstein-all-order-schatten-wall` | `RHTower/PrimeGammaCofinalBocksteinSchattenWall.lean` (5 decls) |

Clause-by-clause audit done (not name-matching): all 10 clauses of card 1, the full equivalence
chain (2) and correction no-go (3) of card 2, and both statements of card 3 are present.  `#print
axioms` on all 32 declarations gives exactly `[propext, Classical.choice, Quot.sound]`.

## Umbrella repairs made to get the final `lake build GaloisForLFunctions.RHTower` green

`lake env lean` per module passed all along; only the area build sees these.  Three genuine
duplicate names among **committed, clean** files (plus one duplicated import line):

1. `RHTower.criticalLinePoint` — identical `1/2 + t*I` in `FiniteDivisorPrefixNonselection` and
   `BurnolHedenmalmUncompletedDomain`.  Renamed the Burnol one to `criticalLineCoordinate`
   (no downstream importers besides the umbrella).
2. `HTGeometry.sqrtWeight` — square-supported arithmetic weight in `SquarefreeClockLaw` vs
   `√w : α → ℂ` in `WeightedDensityL2`.  Renamed the `SquarefreeClockLaw` one to
   `squareSupportedWeight` (its 15 uses are all file-local).
3. `RHTower.Sieve.volume_largeValues_le` — Halász window bound in `HalaszLargeValueWindow` vs the
   classical mean-value bound in `DirichletMeasureLargeValues` (3 downstream users).  Renamed the
   Halász one to `volume_halaszLargeValues_le` (1 caller, `HalaszIntegralBound.lean:138`).
4. `RHTower.lean` imported `PrimeGammaCofinalBocksteinDeterminantTransgression` twice.

After these, `lake build GaloisForLFunctions.RHTower` completed (17488 jobs).

## Standing caveat

`formal_tools.py lint --check-generated` still reports unreachable-module and stale-index errors
that belong to **live concurrent sessions** (prolate/Slepian, CDGA, Halász mean-square).  Those
sessions also commit sweepingly, so your uncommitted work may land in *their* commit — verify with
`git show HEAD:<path>` rather than `git status`.  Regenerating `formal_tools.py index` goes stale
again within minutes while they run.
