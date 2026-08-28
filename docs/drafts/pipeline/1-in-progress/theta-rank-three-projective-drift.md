# Theta rank-three projective drift

- **ID:** S6F-PD
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-current-frontier-map.md` · S6F/TCD finite physical-orbit gate
- **Statement:** On the physical theta source orbit, positivity of one exact projective drift numerator would make native rank-three order-eight curvature strictly increasing and close its remaining finite interval from seam positivity.

## Goal

Prove

```text
thetaCuspReflectedEighthSourceProjectiveDrift x > 0
```

for `0 < x < 137/2000`. This is a source-orbit sign law, not a reformulation assuming rank-three curvature positivity. Existing seam positivity plus the proved derivative identity would then discharge the remaining finite S6F/TCD physical-orbit positivity gate. Cofinal/all-order landing remains separate.

## Gates

- [x] 0 → 1 in-progress: exact source-pure observable and attack target; whole-chamber shortcut already excluded
- [ ] 1 → 2 fully-proven: prove drift positivity on physical interval with no numerical certificate or imported enclosure
- [ ] 2 → 3 formalized: formalize drift sign theorem and interval-to-curvature discharge
- [ ] 3 → 4 publication-ready: integrate with full S6F/TCD landing

## Exact bridge already formalized

`GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveDrift` proves unconditionally:

1. `projectiveValue = sourcePositiveD1Value.re / Q^6` has derivative `projectiveDrift / Q^7`;
2. for `x > 0`, `projectiveValue = 4 * thetaCuspFullReflectionEighthHankelCurvature`;
3. native rank-three curvature has derivative `projectiveDrift / (4 * Q^7)`;
4. since physical `Q > 0`, derivative positivity is equivalent to projective-drift positivity.

The Lean module contains no computation result, decimal, interval certificate, route premise, or added axiom. Targeted build and `#print axioms` pass; theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Approach

Let `P` be the exact source-positive modular polynomial for raw rank-three D1, `L` its exact Lie derivative, and `Q` the literal positive source coordinate. The new numerator is

```text
N = Q * L(P) - 6 * P * L(Q).
```

Attack `N` only on the actual three-state theta trajectory. Search for an exact polynomial shear, invariant cone, barrier, or factorization built from already formalized positive/monotone source coordinates. First finite target is `0 < x < 137/2000`; do not promote to the whole source-positive orthant.

## Hostile audit

- **Killed shortcut:** positivity on the whole source-positive chamber is false; an exact rational seam state already makes the universal source-positive D1 polynomial negative.
- **Current attempted kill:** computation motivated testing the projective normalization, but contributes no theorem. It exposed no sign reversal on the finite physical interval. This is reconnaissance only.
- **Survivor:** exact physical-orbit drift sign. Status: `SURVIVES PRELIMINARY ATTACK`.
- **Next kill tests:** derive `N` explicitly in intrinsic coordinates; search exact admissible source-chamber counterstates; test whether every plausible cone/barrier includes the known negative rational state; inspect endpoint and cusp asymptotics symbolically before attempting interval proof.

## Literature position

Planat--Solé, *Second-Level Concavity of the Riemann Ξ Kernel* (arXiv:2608.19160), uses a related autonomous phase-space, elliptic-monotonicity, and polynomial-shear strategy at rank two. It does not prove this rank-three eighth-order drift sign. Salazar, *Order-Moment Transport and Hankel Determinants in Special-Function Inequalities* (arXiv:2606.31647), develops moment/total-positivity methods but does not supply this physical theta-orbit theorem. No novelty claim is made without a dedicated audit.

## Log

- 2026-08-29 — computation-free projective derivative bridge derived, formalized, targeted-build verified, and reduced to exact physical-orbit sign core.
