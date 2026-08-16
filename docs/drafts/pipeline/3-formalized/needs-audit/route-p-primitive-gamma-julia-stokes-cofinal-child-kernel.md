# Route P primitive Gamma--Julia Stokes cofinal child kernel

- **ID:** `route-p-primitive-gamma-julia-stokes-cofinal-child-kernel`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105K]`
- **Parent:** `route-p-primitive-gamma-julia-physical-stokes-stable-specialization.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCofinalChildKernel.lean`

## Goal

Construct one cofinal prime kernel whose every finite pullback is P-G105I's actual
aperture-transported depth-zero P-G186 matrix, and prove determinant-grade compactness without
discarding off-diagonal incidence.

## Conjecturing loop

### Conjecture 1 — summable transported diagonal may fail to control full Cauchy kernel

**Falsified sharply.** For transported diagonal `w_d(p)`, exact entry law is

```text
|K_d(p,q)|^2 = w_d(p) w_d(q)
  * 64 log(p)^3 log(q)^3 / (log(p)+log(q))^6.
```

Last factor is squared normalized cubic Cauchy coherence and is at most one. Therefore full double
kernel is dominated by product of two summable Stokes weights.

### Conjecture 2 — convenient cofinal formula may only reproduce finite diagonals

**Falsified.** Kernel uses literal P-G186 amplitude, base cubic Cauchy kernel, both prime-log
Jacobians, and both aperture square roots. For arbitrary `p : Fin N -> Nat.Primes`, pullback is
entrywise equal to P-G105I matrix at zero ordinate. No diagonalization or surrogate occurs.

### Conjecture 3 — cofinal limit may lose Hermitian source geometry

**Falsified.** Every two-prime pullback is PSD, hence Hermitian. These two-point identities prove
global kernel equals its Hilbert--Schmidt adjoint. Kernel-to-operator bridge then gives a genuine
self-adjoint Hilbert--Schmidt operator.

## Paper proof

At depth zero, primitive frequency is `log p` and squared von Mangoldt amplitude is `log(p)/p`.
Substituting into cubic Cauchy kernel gives displayed exact Schur law. AM--GM, equivalently strict
cubic coherence theorem with equality branch, bounds coherence by one. P-G105I proves
`Summable w_d` for `d>0`; product majorization proves Hilbert--Schmidt summability on prime pairs.

Finite formula follows by unfolding both diagonal congruences and P-G186 base-Cauchy identity.
Diagonal equals `w_d(p)`, so cofinal diagonal sum is literal oriented Stokes current. Hermitian law
is inherited from actual two-prime PSD pullbacks, and Hilbert--Schmidt adjoint/operator bridge gives
self-adjointness. `QED`

## Novelty and anti-theatre audit

This is missing cofinal compact carrier, not generic determinant infrastructure. It retains every
cross-prime cubic Burnol incidence and gives exact sharp majorant rather than existence-only
compactness. P-G105H divergence is therefore not an off-diagonal obstruction: aperture transport
simultaneously repairs trace and Hilbert--Schmidt mass.

Result does not yet include polar channel, ordinary trace-class proof, trace-restored determinant,
or Xi divisor equality. Those remain mathematical gates.

## Formal status

Lean proves unconditionally:

- exact depth-zero frequency and amplitude identities;
- exact entry norm-square/coherence law;
- coherence bound and product-diagonal majorant;
- Hilbert--Schmidt summability for every positive aperture;
- exact equality of every finite pullback with actual P-G105I matrix;
- exact diagonal and all-prime Stokes trace;
- global Hermitian kernel and self-adjoint represented operator;
- premise-free P-G105K capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Place forced polar ratio in Hellinger/symmetric channel coordinates, prove full physical kernel is
self-adjoint Hilbert--Schmidt (and trace class, not merely diagonally summable), construct
trace-restored entire determinant, identify finite sections with P-G105J determinants, and transfer
upper-half-plane stability to cofinal limit. Then identify complete divisor with Xi without fitting.

## Higher universal principle

Cofinal compactness is projective coherence, not entrywise decay. P-G105H saw divergent marginal
mass before aperture transport; P-G105K shows source-derived Stokes density converts same kernel
into a Hellinger-weighted Cauchy correlation operator. Off-diagonal complexity costs only normalized
coherence at most one. Divergence and compactness are two gauges of same source Gram.

## Log

- 2026-08-16 — Exact cofinal child kernel, sharp Schur bound, Hilbert--Schmidt compactness, literal
  Stokes trace, and self-adjointness paper-proved and formalized.
