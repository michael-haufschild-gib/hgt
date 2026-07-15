# Projective-horizon caustic reflection core

- **ID:** `projective-horizon-caustic-reflection-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN) / REFLECTION-PARITY CERTIFICATE
- **Scientific status:** `[FORMALIZED ALGEBRAIC CORE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper parent:** `hypertranscendental-caustic-divisor-pole-cone`

## Formalized declarations

In `ProjectiveHorizonCausticReflection.lean`:

- `rectangularSchurToeplitz_reflection_eq_conjugate`
- `rectangularSchurToeplitz_det_reflection`
- `rectangularSchurToeplitz_det_eq_zero_of_reflectionFixed`

## Certified content

For any coefficient sequence `h : Nat -> K` over a commutative ring, Lean proves

```text
T_(m,n)((-1)^k h_k)
 =(-1)^n D_m T_(m,n)(h) D_m,
D_m=diag((-1)^0,...,(-1)^(m-1)),                           (1)
```

and consequently

```text
det T_(m,n)((-1)^k h_k)=(-1)^(mn) det T_(m,n)(h).          (2)
```

This is precisely the finite algebraic step required after an analytic functional equation turns
the reciprocal series at `1-s` into the series at `s` with `t` replaced by `-t`.

Lean further proves that a coefficient sequence fixed by this reflection has zero rectangular
determinant whenever `m*n` is odd.  This is the formal symmetry-protected caustic at a reflection
fixed point.

## Verification

The module passes a targeted direct Lean check.  Its declarations use only the standard logical
axioms already present in the imported polynomial and matrix libraries; a scratch `#print axioms`
audit is recorded in the lane verification.  No full build is run.

## Scientific boundary

Formalization certifies the parity identity, not the paper-level analytic pole-order theorem or its
literature novelty.  The parent card is deliberately classified as a bridge: the result translates
classical local multiplicity into the caustic vocabulary but does not clear the dual gate.
