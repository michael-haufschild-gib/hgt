# Real-analytic Dirichlet postcomposition sign rigidity — Lean formalization

- **ID:** `dirichlet-real-analytic-postcomposition-high-line-sign-rigidity`
- **Stage:** `3-formalized`
- **Type:** `[BRIDGE] [NO-GO CLASSIFICATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../../2-fully-proven/not_new_scientific_knowledge/dirichlet-real-analytic-postcomposition-high-line-sign-rigidity.md`

## Generic module

`GaloisForLFunctions.HTGeometry.DirichletAnalyticPostcompositionSignRigidity` formalizes:

- quarter-phase complex-power identities at the first surviving coefficient;
- local Schwarz symmetry from analyticity plus real values on a real neighborhood;
- finite positive analytic vanishing order and a real nonzero leading factor;
- first-coefficient extraction after finite-prefix peeling;
- scaled analytic-postcomposition asymptotics;
- eventual opposite signs on two fixed high horizontal lines for every nonconstant local
  real-analytic scalar germ.

The capstone is
`realLSeriesPostcomp_hasOppositeHighLineSigns_of_eventually_real`.

## Route-I specialization

`GaloisForLFunctions.RHTower.CCMSharpPrimeWindowAnalyticPostcompositionNoGo` proves:

- arbitrary-offset impedance/source line identities;
- nonvanishing of the first nonconstant sharp-window coefficient;
- `exists_high_dyadicSharpPrimeImpedance_analyticPostcomp_both_signs`;
- upper- and lower-half-plane tail no-go capstones for every qualifying analytic germ.

Both modules are wired into their umbrellas. The result kills only scalar analytic
postcomposition. Coefficient-nonlocal square-aperture correlation energy survives.

## Audit

- direct generic-module Lean check: pass;
- direct Route-I specialization Lean check: pass;
- targeted module build: pass;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-declaration scan and `git diff --check`: pass;
- repository lint reached only three unrelated concurrent umbrella failures:
  `DeningerExteriorFreeness`, `DatumQuotient`, and `SupportReindex`; both modules on this card are
  reachable from their theorem-area umbrellas.
