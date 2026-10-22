# Unbounded self-adjoint angular forcing no-go

- **ID:** HB-SA-RESOLVENT-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every tilted exact HC62 source has a unique nonzero forced solution for every unbounded self-adjoint angular operator; self-adjoint spectrum reality forbids only homogeneous eigenmodes.

## Closed route

Killed chain:

`HC62 source nonzero off wall -> self-adjoint one-sector angular exclusion -> source extinction -> shared HB/FZZ-P/PW-B/RBH Ward extinction -> RH`.

For arbitrary complex Hilbert space and arbitrary self-adjoint partial operator `A`, tilted Xi fibre gives `Im lambda(q) != 0`. Self-adjoint resolvent bijectivity yields a unique solution of

`(A-lambda(q))x = source(q)`.

Nonzero Einstein seed and angular profile make both source and solution nonzero, and

`|Im lambda(q)| ||x|| <= ||source(q)||`.

Only homogeneous `A x=lambda(q)x` has no nonzero solution. Thus arbitrary closed unbounded differential operators and self-adjoint boundary domains cannot supply angular-source extinction.

## Positive survivor

Viable producer must prove source-specific zero projection/no-forcing, identify physical equation as homogeneous, or use non-self-adjoint causal/scattering boundary data. Off-wall angular leakage is a stable resolvent response, not a self-adjointness contradiction.

## Novelty audit

Corpus search found no forced-resolvent application to HC62; existing no-gos stopped at Hilbert--Schmidt completions. Second-order Teukolsky literature formulates nonlinear perturbation as a sourced equation with angular/radial mixing; no matching RH route-class theorem found through 2026-08.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBUnboundedSelfAdjointAngularForcingNoGo`
- Closed theorem: `d4HBUnboundedSelfAdjointAngularForcingExclusionRouteKilled`
- Direct `lake env lean`: PASS
- Targeted `lake build`: PASS (`12036` jobs)
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Lint: new module reachable; repository lint remains red only on unrelated pre-existing unwired modules.
