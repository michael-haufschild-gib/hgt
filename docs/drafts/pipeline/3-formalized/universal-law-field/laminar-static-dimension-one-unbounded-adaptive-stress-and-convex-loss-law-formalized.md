# Laminar static dimension one and adaptive stress — Lean certification

- **ID:** ULF-ALG-2
- **Paper card:**
  `../../2-fully-proven/universal-law-field/laminar-static-dimension-one-unbounded-adaptive-stress-and-convex-loss-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveAdversarialLawStress`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

The module formalizes a source-consistent prefix game, not an RH route.

1. `prefixStaticDimensionOne_closed` proves that one prefix-cylinder test is shattered while no
   distinct pair is shattered.
2. `adversarialTranscript_forces_every_round` constructs, for every deterministic policy and every
   depth `d`, one length-`d` final branch whose left-child query truth is the opposite of the policy
   response at every round.
3. `convexAdversarialTranscript_membership` proves that the analogous fractional transcript is
   still realized by one final branch.
4. `convexAdversarialCumulativeLoss_ge_half` proves cumulative loss at least `d / 2` for every
   fractional policy.
5. `constantHalfCumulativeLoss_exact` proves that constant half-prediction has loss exactly `d / 2`
   against every binary label history.
6. `convexAdaptiveMinimaxValue_closed` packages the exact finite-horizon convex value.
7. `constitutiveAdversarialLawStress_closed` is the unconditional capstone.

This certifies ALG Laws I--III and VI in the base fixed-doctrine laboratory: quantifier order and
adaptivity are constitutive resources; static simplicity does not bound legal sequential stress;
convexification changes damage without creating exact closure.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveAdversarialLawStress.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveAdversarialLawStress
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All three checks pass.  Direct elaboration and the owned-module build are warning-free; the umbrella
build has unrelated pre-existing replay warnings.  `#print axioms` on static, deterministic,
convex, and capstone declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.  No
project axiom, `sorry`, `admit`, `opaque`, `unsafe`, numerical computation, or unresolved premise is
used.  Global lint is currently blocked by two unrelated unreachable modules,
`RHTower.Sieve.GhsUniformError` and `HTGeometry.EulerQGammaContinuation`.

## Exact scope

This is a fixed prefix doctrine and therefore only a base calibration.  It does not yet certify
challenge-language growth, admission/effectivity separation, observer contraction, certificate
transport, Hypertranscendence, or an RH statement.  Those are the next field gates; route
applications remain excluded until the mechanism exists independently.
