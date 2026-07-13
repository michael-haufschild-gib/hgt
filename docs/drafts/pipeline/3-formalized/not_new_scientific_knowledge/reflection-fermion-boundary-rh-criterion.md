# Reflection fermion boundary RH criterion

- **ID:** `reflection-fermion-boundary-rh-criterion`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]`, `[FORMALIZATION]`, not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/ReflectionFermionBoundary.lean`
- **Route:** `../../1-in-progress/fermionic-fe-projector-lefschetz-rh.md`

## Statement

Let `sigma` be an involution of an index set and let it act on the integral residue module
`iota -> Z`.  The fermionic boundary

```text
B_sigma = 1 + sigma
```

is injective exactly when every index is fixed.  If `sigma(i) != i`, the explicit nonzero vector
`e_i-e_sigma(i)` lies in its kernel.  If every index is fixed, `B_sigma` is multiplication by two.

For the functional-equation involution

```text
rho |-> 1-conj(rho)
```

on the complete Xi zero set, Lean proves

```text
RH <-> Function.Injective (reflectionFermionBoundary xiZeroReflection).
```

## Scope

This is the exact consumer end of a fermionic/Lefschetz route.  It does not construct the residue
module as cohomology of a source seam complex, contract its anti-invariant part, or prove the
finite-window determinant of `1+J_FE` nonzero.  The result is elementary involution algebra and is
not claimed as new scientific knowledge.
