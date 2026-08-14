# Asymptotic law-core mechanics — formalized

- **Parent:**
  `../../../2-fully-proven/universal-law-field/asymptotic-law-core-mechanics/asymptotic-law-core-formation-affine-exchange-recovery-and-exactification-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCore`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Workflow:** exact module first elaborated with
  `lake env lean /tmp/ConstitutiveAsymptoticLawCore.lean`; tree copy was byte-identical; umbrella
  import added afterward. Direct tree elaboration passed, then the targeted final audit
  `lake build GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCore` completed all 1,781
  required cached/dependency jobs and produced the missing `.olean`. No project, area, or umbrella
  build was run.

## Certified unconditional core

Lean proves:

1. nested tail hulls and nonempty compact-convex asymptotic law cores;
2. exact image exchange for each tail hull and for the complete core under continuous affine maps;
3. exact encoder formation plus decoder reconstruction for every common affine recovery pair;
4. exact action of continuous affine involutions on formed cores;
5. an intertwining functional-equation lift transports the formed recovery packet, reconstructs the
   source involution packet, and has decoded square equal to the identity;
6. a norm-convergent history has singleton law core;
7. asymptotically vanishing affine constraints vanish exactly on the core;
8. approximate affine fixed histories yield exact fixed points throughout the core.

This is a history-formation theorem, not another KL-isometry theorem. It supplies no selector:
functional-equation action is information-neutral, while selection still requires a global
properness law that collapses or excludes noncritical core points.

Scratch `#print axioms` checks for the seven headline formation, exchange, recovery, involution,
lift, kernel-exactification, and fixed-point theorems report only `propext`, `Classical.choice`, and
`Quot.sound`. Repository lint completed its source scan; its only errors concern five unrelated
concurrently added modules missing their own area-umbrella imports. It reported no defect in this
module, which is reachable through `HTGeometry.UniversalLawField`.
