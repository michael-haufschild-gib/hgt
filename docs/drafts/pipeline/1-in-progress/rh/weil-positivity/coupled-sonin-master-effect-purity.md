# Coupled Sonin master-effect purity

- **ID:** `coupled-sonin-master-effect-purity`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE]` exact quantum-information value relation / general corpus strengthening
- **Scientific status:** standard density-operator purity bound transferred to the rectangular
  Hilbert--Schmidt master-effect API; novelty is not claimed
- **Verification status:** source-only by explicit instruction; no Lean process or build run

## Claim

For a rectangular Hilbert--Schmidt channel `C`, put `T = C† C`.  Then

```text
0 ≤ ||T||_HS^2 ≤ ||C||_HS^4,

0 ≤ purity(C) := ||T||_HS^2 / ||C||_HS^4 ≤ 1.
```

The numerator is `Tr(T^2)` and the denominator is `Tr(T)^2`, so this is exactly the order-two
purity of the normalized positive master effect.  The zero channel is assigned purity zero by
the field's zero-division convention.

## General HTGeometry value

`formal/GaloisForLFunctions/HTGeometry/QuantumMasterEffectPurity.lean` adds the rectangular
master-effect purity and proves both the unnormalized inequality and the interval theorem.  It
uses only the Hilbert--Schmidt ideal estimate and the existing operator-norm-to-Hilbert--Schmidt
comparison.  It is independent of zeta, Sonin geometry, finite dimension, and any propagating
flow.

The same file now plugs the relation into the existing square master-constraint trace API:

```text
Re Tr((C† C)^2) ≤ Re Tr(C† C)^2,

purity(C) = Re Tr((C† C)^2) / Re Tr(C† C)^2 ∈ [0,1].
```

Thus consumers using `QuantumMasterConstraintSpectrum` receive the trace theorem directly rather
than reconstructing Hilbert--Schmidt identities at each call site.

The relation strengthens every corpus consumer that constructs a positive effect as `C† C`: the
first two trace values are no longer independent nonnegative numbers.  They obey a quantitative
compatibility law before any spectral comparison or target-moment hypothesis is introduced.

## Direct RHTower consumer

For the coupled all-prime Sonin column `C_a`, write

```text
S_k(a) = Tr((C_a† C_a)^(k+1)).
```

`SoninCoupledPrimeArchGramTransfer.lean` now exposes the exact source theorems

```text
Re S_1(a) ≤ (Re S_0(a))^2,

Re S_1(a) / (Re S_0(a))^2 ∈ [0,1],

Re S_k(a) ≤ Re S_0(a)^(k+1),

Re S_k(a) / Re S_0(a) ≤ Re S_0(a)^k,

P_k(a) := Re S_k(a) / Re S_0(a)^(k+1) ∈ [0,1],

P_(k+1)(a) ≤ P_k(a).
```

The all-order inequalities are the Rényi-replica envelope of the normalized positive effect.
They follow by combining the purity base case with the eigenvalue ceiling
`||C_a† C_a|| ≤ Re S_0(a)` and the existing Hilbert--Schmidt ideal estimate at each replica step.
The one-step estimate is `Re S_(k+1)(a) ≤ Re S_0(a) Re S_k(a)`; after normalization it becomes
monotonicity of the Rényi replica values.

The final inequality acts on every projective coordinate in the live coupled-Gram route.  Any
aperture schedule whose normalized `k`-th moment tends to a positive target must keep the
unnormalized source mass above the corresponding `k`-th-root floor.  This rules out
vanishing-energy approximation schedules and supplies a quantitative compatibility check for
every finite moment block, not only its first nontrivial coordinate.

It does **not** prove the required positive target comparison, construct a suitable aperture
schedule, or prove a prime-power residual nonzero.  It constrains such a schedule once proposed;
no RH implication is claimed.

## Replica Hausdorff strengthening

The later card `quantum-replica-hausdorff-convexity.md` strengthens the decreasing replica
sequence to second complementary finite-difference positivity:

```text
0 <= P_k(a) - 2 P_(k+1)(a) + P_(k+2)(a).
```

The new result is again a direct master-effect theorem, not a zeta-specific wrapper.  Its exact
even/odd Hilbert--Schmidt-square factorizations are now in
`HTGeometry/QuantumReplicaHausdorff.lean`, with direct coupled Sonin consumers in
`SoninCoupledPrimeArchGramTransfer.lean`.  The route audit there records why source-mass control is
still required before the relation can constrain the canonically rescaled target moments.

## Physics provenance

- A. K. Ekert, C. M. Alves, D. K. L. Oi, M. Horodecki, P. Horodecki, and L. C. Kwek,
  *Direct estimations of linear and nonlinear functionals of a quantum state*, Physical Review
  Letters 88 (2002), 217901,
  [DOI 10.1103/PhysRevLett.88.217901](https://doi.org/10.1103/PhysRevLett.88.217901).
  The paper identifies `Tr(ρ²)` as directly measurable quantum-state purity and treats nonlinear
  density-operator functionals without full tomography.

## Verification status

Source inspection only.  Under the active user constraint, no Lean invocation, scratch
compilation, lint, numerical check, targeted build, or full build was run.  The declarations stay
in stage 1 until a narrow validation pass is authorized.
