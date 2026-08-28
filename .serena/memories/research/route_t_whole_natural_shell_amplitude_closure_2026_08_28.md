# Route-T whole natural-shell amplitude closure (2026-08-28)

Lean-closed modules:
- MaynardElevenFifthsTrivialBoundaryAtomExclusion: exact trivial-boundary receiver now covers mu <= 11/5; removes false alpha >= 3/4 floor.
- MaynardTrivialBoundaryShellCapStructural: canonical dyadic cap works for every fixed support exponent mu < 4, strictly.
- MaynardFullAmplitudeMeasureAssembly: exact measure union for base plus all capped dyadic bands.
- MaynardNaturalShellAllBandFirstExclusion: one scalar selector budget excludes first receiver for all bands.
- MaynardNaturalShellFullMeasure / SelectorMeasure: full natural-shell bad-measure bound.
- MaynardFixedWidthNaturalShellFullMeasure: actual rung/shell-divided defect, selector cost discharged internally.

Final theorem:
RHTower.Sieve.eventually_volume_routeT_fixedWidth_canonicalNaturalShell_full_forcedSecond

Target build passed:
lake build GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthNaturalShellFullMeasure

Axiom audit: only propext, Classical.choice, Quot.sound.

Frontier map remained read-only. Card updated:
docs/drafts/pipeline/1-in-progress/route-t-maynard-fixed-width-gap-shell-assembly.md

Remaining Route-T burden:
sum whole-shell bounds over finite rung/natural-shell cover, add low packet, then combine with ordered-prime occupancy without losing strict sub-3/2 moment exponent.