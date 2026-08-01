# Zeta–Stone singular–infinitary reconstruction law

- **ID:** `zeta-stone-singular-infinitary-reconstruction-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM / ZETA SOURCE-FIBRE CLASSIFICATION / POSITIVE RESOLUTION
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT RH] [EXTERNAL NOVELTY PROVISIONAL]`
- **Publication target:** `riemann-source-modular-superselection`

## Theorem

Two unconditional constructions meet at one reconstruction boundary.

### A. Stone universality inside one zeta-divisor fibre

For every pointed compact metrizable totally disconnected space `(S, s₀)`, a countable sparse
prime-sign system produces meromorphic Euler sources on `Re s > 0` such that:

1. the anchor source is the Riemann zeta function;
2. every source has the complete signed zeta divisor, pointwise and with multiplicity;
3. the recurring prime-tail pattern chamber is homeomorphic to `S`, with `s₀` mapped to the
   all-positive pattern;
4. every observable depending only on the positive-half-plane divisor is constant on the source
   family.

The containing exponent-zero Euler-gauge quotient has dense leaves and indiscrete topology. No
continuous global leaf selector exists, and every nonconstant separated leaf invariant is nowhere
continuous.

### B. Complete positive finite/infinite phase transition

For every `K ≥ 12`, the `K`-free integers and exact largest-valuation shells `K, K+1, ...` form a
pairwise-disjoint `0/1` partition of all positive integers. Their Dirichlet channels factor as
zeta times normalized multipliers. Every multiplier is a holomorphic unit on `Re s > 1/2`, so
every channel has the exact zeta zero divisor there. The normalized family is jointly
differentially independent over the full zeta differential field, while its finite prefixes
telescopically converge to the exact identity, uniformly on every closed half-plane in `Re s>0`.

### C. Reconstruction law

Divisor-only source inversion cannot separate Stone source geometry. Continuous gauge selection
is impossible. Finite differential algebra cannot witness the exact completion identity. The
surviving reconstruction operation must therefore be source-pointed, singular across the gauge
quotient, and countably locally normal after finite algebra becomes blind.

## Formal theorem map

- `RHTower.zetaStone_completePositiveHalfPlaneDivisor_eq`
- `RHTower.zetaStone_anchor_eq_riemannZeta`
- `RHTower.zetaStone_recurringPatternChamber_eq`
- `RHTower.zetaStone_divisorProfile_constant`
- `GaloisForLFunctions.HTGeometry.not_exists_continuous_exponentZeroEulerGaugeSelector`
- `GaloisForLFunctions.HTGeometry.nowhereContinuousAt_of_nonconstant_exponentZeroEulerGaugeInvariant`
- `RHTower.completePositiveKolchinFreeRiemannResolution`
- `RHTower.completeResolutionMultiplier_uniformOn_rightHalfPlane`

Primary modules:

- `formal/GaloisForLFunctions/RHTower/ZetaStoneIsodivisorialSource.lean`
- `formal/GaloisForLFunctions/HTGeometry/IsodivisorialPrimeWalshStoneSaturation.lean`
- `formal/GaloisForLFunctions/HTGeometry/EulerGaugeSingularIncidenceLaw.lean`
- `formal/GaloisForLFunctions/RHTower/CompletePositiveKolchinFreeRiemannResolution.lean`

## Significance boundary

Grosswald–Schnitzer same-zero Euler products and Helson-zeta prescribed-divisor theorems are
essential prior art. The novelty claim is not mere divisor cloning, the elementary `K`-free
identity, or telescoping. It is the combined exact object:

- arbitrary pointed Stone recurrence geometry within one fixed complete zeta-divisor fibre;
- a complete positive disjoint coefficient resolution with the same zeta zero divisor in every
  channel;
- maximal relative finite differential rank together with one exact countable normal closure;
- a proved impossibility of continuous source selection.

No zero exclusion is claimed. A hypothetical off-line zeta zero occurs in every positive channel
with unchanged multiplicity. The theorem classifies what a new RH route must preserve before
divisor-only or finitary scalarization.

## Verification gates

- [x] paper proof written
- [x] zeta-instantiated Stone connector compiled in isolation
- [x] complete positive resolution compiled previously in isolation
- [ ] isolated `#print axioms` audit after shared Lean processes finish
- [ ] full formal lint
- [ ] targeted final umbrella build
- [ ] specialist novelty review
- [ ] rendered manuscript antagonist review

## Log

- 2026-08-01 — combined exponent-zero gauge foliation, pointed Stone saturation, actual zeta
  continuation, and complete positive Kolchin-free resolution into the singular–infinitary
  reconstruction law. Replaced omnibus headline theorem in manuscript with this falsifiable
  three-part result.
