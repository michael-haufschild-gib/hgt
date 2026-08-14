# Strict-convex law-core selection — formalized

- **Parent:**
  `../../../2-fully-proven/universal-law-field/asymptotic-law-core-mechanics/strict-convex-nonlinear-exchange-dissipation-and-global-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCoreRigidity`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Workflow:** theorem was developed and closed first in
  `/tmp/ConstitutiveAsymptoticLawCoreRigidity.lean`; tree file was synchronized byte-for-byte;
  direct tree elaboration then passed. Targeted final audit
  `lake build GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCoreRigidity` built only leaf
  and required cached dependencies, completed 1,782 jobs, and produced missing `.olean`. No area,
  umbrella, or project build was run.

## Certified mechanism

Lean proves:

1. continuous convex energy converging to `c` is at most `c` on whole formed law core;
2. every non-singleton law core under continuous strictly convex convergent energy contains an
   explicit midpoint law with energy strictly below `c` and outside scalar energy core;
3. every compact formation satisfies exact singleton-or-dissipation alternative;
4. compact sublevels of globally continuous strictly convex energy generate required compact
   formation carrier from energy convergence alone;
5. nonlinear no-loss inclusion forces source law core to be singleton;
6. exact nonlinear formation exchange therefore forces selection;
7. global compact-sublevel properness plus nonlinear no-loss selects without a pre-given compact
   carrier.

This closes global formation/properness theorem at abstract field level. It does not insert an
RH-specific energy or assume arithmetic source satisfies nonlinear no-loss.

Scratch `#print axioms` checks for all seven headline theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. Module contains no `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, computation certificate, or enlarged heartbeat.
