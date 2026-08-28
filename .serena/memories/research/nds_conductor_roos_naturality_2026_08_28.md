NDS hard-frontier result (2026-08-28).

User constraint: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is read-only; do not edit it.

New Lean modules:
- `formal/GaloisForLFunctions/RHTower/XiReducedConductorRoosRegulatorClassification.lean`
- `formal/GaloisForLFunctions/RHTower/XiNodalConductorHolonomyNaturalityClassification.lean`

Structural results:
1. `nonempty_xiReducedConductorRoosRegulator_iff_riemannHypothesis`: any regulator factoring the actual transverse Roos class through the reduced multiplicity-conductor nearby class exists iff RH. No linearity/continuity/monodromy premise is used. Reason: reflected Xi fibres have identical reduced conductor input but opposite Roos output.
2. `canonicalXiOrientedConductorRoosRegulator`: adding one actual theta terminal-jet holonomy coordinate reconstructs the coefficient-faithful Roos class unconditionally.
3. `everyXiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff_riemannHypothesis`: the arithmetic/Picard--Lefschetz naturality square on actual nonzero terminal conductor classes commutes globally iff RH.

Interpretation: reduced NDS conductor-factorization is retired as circular at RH strength. Oriented repair is unconditional but preserves the transverse obstruction. Exact open NDS core is a genuinely new source theorem forcing arithmetic monodromy to agree with Picard--Lefschetz monodromy; this is equivalent to RH, not yet proved.

Card:
`docs/drafts/pipeline/5-failed/nds-reduced-conductor-roos-regulator-classification.md`

Wiring/audit:
- Both modules imported by `formal/GaloisForLFunctions/RHTower.lean`.
- Targeted `lake env lean` and `lake build` passed for each leaf module.
- `scripts/check_axioms.sh` expanded to 356 declarations and passed; new capstones use only `[propext, Classical.choice, Quot.sound]`.
- Scoped diff check and forbidden-declaration scan clean.
- Corpus index refreshed; research search resolves new declarations.
- No stale Lean/Lake processes.
- Full umbrella build deliberately not run.