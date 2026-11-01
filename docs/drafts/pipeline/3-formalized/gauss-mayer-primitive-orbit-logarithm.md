# Primitive-orbit logarithm of the actual Mayer determinant

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [primitive modular orbit product](gauss-mayer-primitive-orbit-product.md).
- **Input:** [actual primitive-coordinate traces](gauss-mayer-primitive-orbit-words.md).

## Theorem

Let `c` range over primitive digit-pair cycles, with pair length `ℓ(c)>0`
and actual expanding multiplier `λ_c>1`. Define

```text
J(w,z) = Σ_c Σ_(r≥1) z^(2rℓ(c))/r · (λ_c^r)^(−w)/(1−(λ_c^r)⁻²).
```

For each `Re w>1`, this double series converges absolutely on a neighborhood
of `z=0`, and the actual global determinant satisfies

```text
D(w,z) D(w,−z) = exp(−J(w,z)).
```

Both conclusions hold throughout `|z|≤1` when `Re w>2`.

## Proof

The certified bijection sends each actual even source word to unique data
`(c,r,i)`, where `0≤i<ℓ(c)`. Its trace-series term is independent of `i`:

```text
A(c,r) = z^(2rℓ(c))/(rℓ(c)) · (λ_c^r)^(−w)/(1−(λ_c^r)⁻²).
```

There are precisely `ℓ(c)` distinct root positions. Their finite sum is
`ℓ(c)A(c,r)`, equal to the displayed summand of `J`. Their summed norms
are `ℓ(c)|A(c,r)|=|ℓ(c)A(c,r)|`, so this finite regrouping preserves the
complete absolute mass exactly.

Transport the certified full word-series norm summability through the
source bijection. Nonnegative Fubini gives summability of the rotation-fiber
norm sums, hence absolute summability over `(c,r)`. Complex Fubini then
identifies the original even-word exponent with `J`. Substituting into the
certified determinant identity proves the local statement; using the
certified closed-unit-disk word bound proves the second domain.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerPrimitiveOrbitTrace.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitTrace`.

- `repetitionTerm`, `orbitExponent`: literal primitive-cycle logarithm.
- `exists_signed_determinant_eq_orbitExponent`: local identity and absolute convergence.
- `signed_determinant_eq_orbitExponent_on_closed_unit`: closed-unit identity and absolute convergence.

Direct production check passed without diagnostics. Both transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The
programme umbrella imports the module.

## Scope

This completes the countable primitive-cycle regrouping, including its exact
`1/r` coefficient. Geometric denominator expansion and the
[Euler product](gauss-mayer-primitive-orbit-product.md) are also certified. No geometric length, scattering identity,
or critical-strip resonance exclusion is asserted.
