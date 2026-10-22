# Lueders--Kadison transition defect

- **ID:** `luders-kadison-transition-defect`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE]` exact physics value relation / general corpus strengthening
- **Scientific status:** known operator inequality specialized to an exact two-sector identity;
  novelty is not claimed
- **Verification status:** source-only by explicit instruction; no Lean process or build run

## Claim

For an idempotent cutoff `e`, let

```text
Phi_e(X) = e X e + (1-e) X (1-e),
R = (1-e) X e,
U = e X (1-e).
```

Then the square-multiplicativity defect of the two-outcome pinching is exactly

```text
Phi_e(X^2) - Phi_e(X)^2 = U R + R U.
```

If `e` and `X` are self-adjoint, `U=R^dagger` and `R=U^dagger`, so

```text
Phi_e(X^2) - Phi_e(X)^2 = R^dagger R + U^dagger U.
```

Thus every state `psi` has the value identity

```text
Re <psi, (Phi_e(X^2)-Phi_e(X)^2) psi>
  = ||R psi||^2 + ||U psi||^2 >= 0.
```

The usual Kadison--Schwarz inequality gives positivity of the defect.  The two-outcome block
structure gives the stronger equality with the two oriented transition-channel energies.

## General HTGeometry value

`formal/GaloisForLFunctions/HTGeometry/TwoOutcomePinchingKadison.lean` adds:

- `twoOutcomePinching` and `twoOutcomePinchingKadisonDefect`;
- lower and upper transition channels;
- the exact algebraic transition-product identity;
- its decomposition into two quantum master constraints;
- the statewise sum-of-squared-amplitudes identity and automatic nonnegativity.

The file is imported by the `HTGeometry` umbrella.  It is independent of zeta, Sonin geometry,
finite dimension, and any flow.  It can be reused by every constraint module that has a
self-adjoint idempotent sector selector.

## Direct RHTower consumer

`SoninLudersPinching.lean` identifies the established RHTower `ludersPinching` with the new general
pinching and rewrites the defect in the existing `crossBoundary` / `upperBoundary` language.  For
the actual central Sonin projection `Q_a` and symmetric physical dilation signal `D_p`, source
declarations now state

```text
Phi_(Q_a)(D_p^2) - Phi_(Q_a)(D_p)^2
  = master((1-Q_a) D_p Q_a) + master(Q_a D_p (1-Q_a)),
```

together with the corresponding statewise norm-square equality.  The self-adjointness of `D_p`
is also exposed as a reusable theorem rather than reconstructed at each consumer.

This strengthens the live cutoff calculus in three concrete ways:

1. a pinching-positivity premise is replaced by an exact sum of existing master constraints;
2. the new positive observable plugs directly into the master-constraint spectrum, trace, Ward,
   and physical-state-kernel APIs;
3. the same relation applies at every retained prime-power dilation scale without a separate
   compactness or spectral hypothesis.

It does **not** prove that the principal-subtracted Sonin residual is nonzero.  The identity
controls the full actual transition channel; subtracting the non-idempotent formal complement is
still the live nondegeneracy problem.  Therefore no RH implication is claimed.

## Physics provenance

- G. Lueders, *Ueber die Zustandsaenderung durch den Messprozess*, Annalen der Physik 443
  (1950), 322--328,
  [DOI 10.1002/andp.19504430510](https://doi.org/10.1002/andp.19504430510).
  This is the original projective measurement state-change rule underlying the two-block
  nonselective pinching.
- R. V. Kadison, *A Generalized Schwarz Inequality and Algebraic Invariants for Operator
  Algebras*, Annals of Mathematics 56 (1952), 494--503,
  [DOI 10.2307/1969657](https://doi.org/10.2307/1969657).
  This supplies the encompassing positive-map Schwarz defect; the source identity above computes
  that defect exactly for a two-outcome pinching.

## Scattering/Feshbach audit

`[ROUTE RETIRED]` The bounded optical theorem already present in `FiniteConstraintGroupAverage`
requires an actual unitary scattering defect `U-1`.  The principal-subtracted Sonin response is a
difference of two boundary channels, and neither that difference nor the formal-complement
channel is unitary.  Recasting it as `U-1` would add exactly the missing structure as a hypothesis.

The operator Feshbach formula likewise requires a genuine projection split and an invertible
eliminated resolvent block.  The source comparison cutoff is proved non-idempotent, so it does not
supply that split; no source theorem supplies the required inverse.  The scalar vacuum Feshbach
API remains useful for moment forms, but applying it to this operator residual would introduce
new projection and resolvent premises rather than discharge one.  Consequently neither standard
physics identity acts directly on the principal-subtracted residual.  The exact Lueders--Kadison
transition defect above is the strongest hypothesis-free statement available from these lanes.

## Verification status

Source inspection only.  Under the active user constraint, no Lean invocation, scratch
compilation, lint, numerical check, targeted build, or full build was run.  The declarations stay
in stage 1 until a narrow validation pass is authorized.
