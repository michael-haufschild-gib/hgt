# Real-analytic Dirichlet postcomposition sign rigidity — Lean certificate

- **ID:** `dirichlet-real-analytic-postcomposition-high-line-sign-rigidity`
- **Stage:** `3-formalized`
- **Type:** `CERTIFICATE (Lean 4) / [BRIDGE] [NO-GO CLASSIFICATION]`
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [UNCONDITIONAL] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `dirichlet-real-analytic-postcomposition-high-line-sign-rigidity.md`

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

Its eventual two-line conclusion is the literal paper theorem: for any requested height `H`, choose
the horizontal parameter `x > H + 1` in the two eventual sign filters and set
`z_+(x) = tau + i(x - 1)` and `z_-(x) = -tau + i(x - 1)`.  Then
`1 - i z_+(x) = x - i tau` and `1 - i z_-(x) = x + i tau`, so both signs occur above `H`.

## Route-I specialization

`GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowAnalyticPostcompositionNoGo` proves:

- arbitrary-offset impedance/source line identities;
- nonvanishing of the first nonconstant sharp-window coefficient;
- `exists_high_dyadicSharpPrimeImpedance_analyticPostcomp_both_signs`;
- upper- and lower-half-plane tail no-go capstones for every qualifying analytic germ.

Both modules are wired into their umbrellas. The result kills only scalar analytic
postcomposition. Coefficient-nonlocal square-aperture correlation energy survives.

## Audit

- direct `lake env lean GaloisForLFunctions/HTGeometry/DirichletAnalyticPostcompositionSignRigidity.lean`: pass;
- direct `lake env lean GaloisForLFunctions/RHTower/CCM/CCMSharpPrimeWindowAnalyticPostcompositionNoGo.lean`: pass;
- targeted `lake build GaloisForLFunctions.HTGeometry.DirichletAnalyticPostcompositionSignRigidity`: pass;
- targeted `lake build GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowAnalyticPostcompositionNoGo`: pass;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
