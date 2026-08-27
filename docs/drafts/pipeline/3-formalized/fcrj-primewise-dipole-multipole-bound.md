# FCRJ primewise dipole multipole bound

- **ID:** FCRJ-PDMB
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-formalized)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 62
- **Statement:** Physical endpoint measure is exactly neutral and its unresolved Fourier packet is
  controlled by weighted primewise endpoint chord, not absolute endpoint mass.

## Goal

Define

```text
W = sum_(p in P) a_p,
D = sum_(p in P) a_p |z_end(p)-z_start(p)|,
a_p = log(p)/p.
```

For physical endpoint moment `U_n`, prove unconditionally

```text
sum_x j_x = 0,                                           (DM1)
|U_n| <= n D,                                            (DM2)
|U_n| <= min(n D, 2W).                                   (DM3)
```

## Gates

- [x] 0 → 1 in-progress: corpus search, primary-literature audit, frozen source statement
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile constant audit
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. `sum_endpointCircleJump_mul` gives exact primewise endpoint difference for every test function.
2. `norm_pow_sub_pow_le_of_norm_one` proves `n`-Lipschitz power map on unit circle.
3. `ClusteredExponentialMomentAnnihilator` shows abstract higher moment cancellation but does not
   identify physical coefficients.
4. Loop 61 charges unresolved endpoint pairs by full pair mass; corpus has no theorem replacing
   that cost by physical primewise dipole chord.

## External frontier `[LITERATURE]`

Zero-mass signed-measure Fourier bounds by first transport moment are classical
Kantorovich--Rubinstein infrastructure.  Targeted search found no clipped prime-log aperture
identity `(DM1)--(DM3)` and no use of exact primewise dipoles in FCRJ ultraviolet resolution.
Novelty claim is restricted to coefficient-faithful physical specialization and route impact.

## Conjecture loop A — arbitrary endpoint clusters

`[TOO WEAK]` Abstract zero-sum cluster assumptions do not follow for an arbitrary chosen cluster
partition and would add a premise disconnected from source.

## Conjecture loop B — literal primewise dipoles

`[CONJECTURE] [FROZEN 2026-08-27]` `(DM1)--(DM3)` hold for the actual physical endpoint source.

### Paper proof plan

Take constant test function in `sum_endpointCircleJump_mul`; every prime contributes `a_p(1-1)`,
proving `(DM1)`.  For `f(x)=fourier_1(x)^n`, same exact identity gives

```text
U_n = sum_p a_p (z_end(p)^n-z_start(p)^n).
```

Unit-circle power Lipschitz gives each difference at most
`n|z_end(p)-z_start(p)|`; triangle inequality proves `(DM2)`.  Trivial unit norm gives bound
`2a_p`; take minimum of two aggregate bounds for `(DM3)`.

### Hostile audit

- No activity, separation, noncollision, or RH premise is used.
- Clipped boundary identification is already handled by exact circle aggregation theorem.
- `D=0` forces every moment to vanish, as required for collapsed prime intervals.
- Bound is first-order and cannot exploit cancellation between different prime dipoles.
- It is pointwise in `n`; conversion to an inverse-square tail needs a low/high frequency split.

Verdict: `PROVED ON PAPER`.  Abstract Lipschitz fact is classical; exact physical
primewise dipole moment and replacement of unresolved endpoint mass by `D` are candidate-new.

## Open core

Lean formalization is complete in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointDipoleMultipoleBound.lean`.
Direct checking, targeted build, `#print axioms` audits, umbrella wiring, and global formal lint
pass; capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Next combine
`(DM3)` with inverse-square tail splitting to price unresolved physical clusters by `N W D`
rather than full pair mass.
