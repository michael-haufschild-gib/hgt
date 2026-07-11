# Per-test nonnegative limits are exactly the RH sign condition

- **ID:** `per-test-nonnegative-limit-rh-equivalence`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** `XiTraceHankelCountableCriterion.lean` and
  `countable-semilocal-gram-diagonal-to-rh.md`
- **Statement:** Allowing an arbitrary nonnegative scalar sequence for each integer polynomial,
  with limit equal to its Xi trace-Hankel value, is equivalent to integer-polynomial
  trace-Hankel nonnegativity and hence to RH.

## Goal

Separate the logical sign content of a per-test Gram approximation from the source-side structure
that could make such an approximation a proof. The theorem is an audit result: it proves that
polynomial-dependent nonnegative limits do not by themselves weaken the RH-bearing assertion.

## Paper proof

Let `Q(P)` be the real Xi trace-Hankel value. If

```text
e_j(P) >= 0  for every j,
e_j(P) -> Q(P),
```

then closedness of the nonnegative real half-line gives `Q(P)>=0`.

Conversely, if `Q(P)>=0`, the constant sequence `e_j(P)=Q(P)` is nonnegative and converges to
`Q(P)`. Therefore

```text
for every P, Q(P) is a limit of nonnegative scalars
  <->
for every P, Q(P)>=0.
```

The existing countable criterion identifies the right side with RH.

## Route consequence

A family of kernels `K(P,j)` with no relation between different polynomials contributes only the
scalar sequence `||K(P,j)||_HS^2`. It does not encode the mixed anti-diagonal moment in a two-term
polynomial unless the kernel construction is coefficient-linear, or at least has a stated
polarization law on one common carrier.

The minimal non-oracular replacement is finite-degree coherence. For each degree `d` and cutoff
`j`, construct one source-defined linear map from coefficient vectors to a common Hilbert--Schmidt
space. Its Gram entries must converge to the Xi Hankel block

```text
[xiCentralReciprocalMoment (m+n)]_(0<=m,n<=d).
```

The carrier, cutoff, and renormalization may depend on `d`; no universal all-degree moment operator
is required. They may not depend on the sign of `Q(P)` or on the Xi divisor.

## Gates

- [x] 0 -> 1: unrestricted per-test scalar-limit statement isolated
- [x] 1 -> 2: closed-cone proof and constant-sequence converse complete
- [x] 2 -> 3: formalized as
  `xiCentralTraceHankelIntNonnegativeLimit_iff_nonnegative` and
  `xiCentralTraceHankelIntNonnegativeLimit_iff_riemannHypothesis`
- [ ] 3 -> 4: not publication-targeted; this is a route guardrail

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiTraceHankelCountableCriterion.lean` -- pass
- `lake build GaloisForLFunctions.RHTower.XiTraceHankelCountableCriterion` -- pass
- both new theorems have axioms `[propext, Classical.choice, Quot.sound]`

## Scientific status

This is elementary closed-cone reasoning and is not new scientific knowledge. Its value is exact
route control: it prevents a target-dependent scalar square root or arbitrary polynomial-wise
factorization from being mistaken for a source Gram mechanism.

## Log

- 2026-07-11 -- paper audit proved and Lean endpoint formalized.
