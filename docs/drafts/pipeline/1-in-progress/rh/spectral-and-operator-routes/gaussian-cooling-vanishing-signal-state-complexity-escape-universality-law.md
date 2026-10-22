# Gaussian cooling vanishing-signal/state-complexity escape universality law

- **ID:** `gaussian-cooling-vanishing-signal-state-complexity-escape-universality-law`
- **Law:** LAW497
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/GaussianCoolingVanishingSignalStateComplexityEscapeUniversalityLaw.lean`

## Theorem

Let `J : ℝ → ℝ` be continuous and bounded, with `J 0 > 0`.  Write

```text
m_tau(k) = ∫ x^k exp(-tau x^2) J(x) dx.
```

Then:

1. every fixed coordinate vanishes under cooling:

   ```text
   m_tau(k) -> 0  as tau -> infinity;
   ```

2. for every fixed hidden-state dimension `d`, cofinally in `tau`,

   ```text
   m_tau ∉ FixedStateSpaceDimensionLocalClosure(d).
   ```

Thus the observations converge pointwise to the zero sequence while their exact/local-cofinal
linear realization dimension escapes every fixed finite bound.  Signal amplitude and hidden-state
complexity move in opposite directions.

## Theorem-generated derivation

This law was not predicted and then searched.  Whole-corpus leaf pairing exposed:

- `GaussianWindowMomentRescaling.weightedMoment_eq_cooled`;
- `GaussianWindowMomentRescaling.tendsto_gaussianCooledMoment`;
- `GaussianWindowHankelRecession.gaussianWindow_momentHankelMatrix_posDef_eventually`;
- `FiniteStateSpaceHankelRank.not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero`.

For fixed `k`, rescaling gives

```text
m_tau(k) = (sqrt tau)^(-(k+1)) K_tau(k),
```

where `K_tau(k)` converges to the finite Gaussian moment
`J(0) ∫ y^k exp(-y^2) dy`.  Since `k+1 > 0`, the scale tends to zero, proving coordinatewise
vanishing.  For fixed `d`, recession makes the Hankel block of size `d+1` positive definite for all
sufficiently large `tau`; its determinant is therefore positive.  The finite-state Hankel law says
every sequence in the fixed-`d` local closure has zero determinant at that size, giving the
contradiction.

No numerical computation is used.

## Strict corpus delta

The Gaussian recession card proves eventual positive-definiteness but does not connect it to
arbitrary nonnormal finite state-space realizations or prove pointwise signal collapse.  The
finite-state card proves the abstract determinant obstruction but does not instantiate the
sign-changing Gaussian cooling family.  Their combination exposes a singular-limit law absent from
both: pointwise convergence to a rank-zero signal does not bound, or even prevent divergence of,
the realization complexity of the approximating family.

## Post-proof novelty audit

Performed only after the dependency-closed Lean proof passed.

- Cooper--Fickes, [*Recurrence Ranks and Moment
  Sequences*](https://arxiv.org/abs/2101.00302), develops moment rank, recurrence rank, Hankel
  factorizations, and finite-atomic representations, but not this Gaussian cooling family or the
  vanishing-signal/escaping-state limit.
- Berg--Szwarc, [*A determinant characterization of moment sequences with finitely many
  mass-points*](https://arxiv.org/abs/1405.7267), proves the classical positive-Hankel
  finite/infinite-support boundary, but not sign-changing densities that become finite-section
  positive under cooling or the simultaneous pointwise-zero limit.
- Deng--Yang--Qian, [*A Moment--Hankel Rank Method for Identifying the Number of Point Sources in
  the Heat Equation*](https://arxiv.org/abs/2606.21815), uses a low-frequency limit to obtain a
  finite exponential sequence whose Hankel rank counts finitely many sources.  Its direction is
  opposite: the limiting sequence is finite-rank, whereas LAW497 has every coordinate tending to
  zero while arbitrarily deep nonzero Hankel minors persist cofinally before the limit.

Targeted searches for Gaussian-window Hankel concentration, pointwise-zero moment families with
unbounded Hankel/state rank, and realization order divergence under vanishing signals found the
component theories but no statement of this exact law.  Verdict:
`[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Generic rank discontinuity is elementary; novelty is
claimed only for the exact bounded continuous, possibly sign-changing Gaussian cooling theorem and
its local-cofinal arbitrary-state-space conclusion.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean` passed
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
