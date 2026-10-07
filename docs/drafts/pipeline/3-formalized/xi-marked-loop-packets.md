# Finite loop packets in the actual marked Xi source

- **ID:** RH-XILP-20261007
- **Stage:** 3-formalized
- **Parent:** `../1-in-progress/xi-logarithmic-islands-monodromy.md`
- **Verdict:** BRIDGE; novelty uncertified; joint finite-image equality remains open in Lean

## Exact endpoint

For a finite real slope set A, selected a in A, arbitrary real R, and any
finite packet of loops in C minus {0,-1} based at a common point, each with
zero winding around zero, there is a common source point s with Re(s)>R
and loops based at s in the actual source

    {s : xi(s) != 0 and d_b(s) != -1 for every b in A},
    d_b(s) = xi(s)*exp(-b*s).

The a-coordinate maps these loops exactly to the given packet, after the
proved endpoint identification. Every other coordinate is nullhomotopic.
The source is path connected and contains 0, where all coordinates equal1/2.
No inverse-island, regular-value, zero-location, or RH premise remains.

## Dependency-closed proof

Zero exponential-cover degree closes each logarithmic lift. Translate these
lifts by a logarithm of the common target basepoint. A finite union of compact
path images, together with that logarithm itself, lies in one disk. The extra
singleton handles an empty packet. The separated actual Xi inverse disk
realizes the selected loops. Other coordinates avoid the unit circle on the
whole logarithm disk and extend over that contractible disk, so their loops
are nullhomotopic. Countability of the excluded entire-function zero sets
gives path connectedness of the actual source.

Two reusable bridges are included: explicit fundamental-group transport and
common-conjugator comparison; and the finite-group fact that if every finite
subset of a normal subgroup N has a common conjugate inside H, then q(N) is
contained in q(H) for every homomorphism q to a finite group. Surjectivity of
q is unnecessary. The latter bridge has not yet been assembled with the
actual Xi packet endpoint into the full joint finite-image equality.

## Formal audit

- `HTGeometry/ClosedLogarithmicLoops.lean`: three public declarations.
- `HTGeometry/FiniteNormalPackets.lean`: one public declaration.
- `HTGeometry/FundamentalGroupTransport.lean`: seven public declarations.
- `RHTower/XiMarkedSourceSpace.lean`: thirteen public declarations.
- `RHTower/XiMarkedLoopPackets.lean`: one public declaration.

Targeted builds and all five actual-source `lake env lean` checks pass.
All25 public axiom closures contain only propext, Classical.choice, Quot.sound.
Each leaf is imported once by its theorem-area umbrella. No admissions or
heartbeat changes. Matching proof scratches removed after final checks.

Evidence: `/tmp/rh-marked-packet-build.log`,
`/tmp/rh-final-ClosedLogarithmicLoops.log`,
`/tmp/rh-final-FiniteNormalPackets.log`,
`/tmp/rh-final-FundamentalGroupTransport.log`,
`/tmp/rh-final-XiMarkedSourceSpace.log`,
`/tmp/rh-final-XiMarkedLoopPackets.log`, `/tmp/rh-marked-packet-axioms.log`.

Index refreshed. Global lint fails on five unrelated unreachable HTGeometry
modules: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No own-leaf lint error;
global gate is not clean. Evidence: `/tmp/rh-marked-packet-index.log` and
`/tmp/rh-marked-packet-lint.log`.
