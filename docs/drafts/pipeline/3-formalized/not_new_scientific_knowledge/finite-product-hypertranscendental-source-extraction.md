# Finite-product hypertranscendental source extraction

- **ID:** `finite-product-hypertranscendental-source-extraction`
- **Stage:** 3-formalized
- **Type:** REUSABLE DIFFERENTIAL-ALGEBRA CLOSURE AND SOURCE LAW
- **Scientific status:** `[KNOWN CONSEQUENCE] [LEAN-FORMALIZED] [CORPUS-STRENGTHENING]`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/FiniteDifferentialCircuitBoundary.lean`

## Theorem

Let `E/F` be a differential field extension in characteristic zero and let `f_i` be a finite family
of elements of `E`.  Then

```text
(forall i, f_i is DA over F) => product_i f_i is DA over F,
```

and therefore

```text
product_i f_i is HT over F => exists i, f_i is HT over F.
```

The converse is false: HT factors may cancel, for example through an inverse pair.  The theorem is
a source-localization law, not an equivalence.

Lean declarations:

- `differentialAlgebraicOver_finset_prod`;
- `exists_hypertranscendental_factor_of_finset_prod`;
- `exists_hypertranscendental_factor_of_eq_finset_prod`.

The product closure was previously specialized inside `MeromorphicGammaReflection.lean`.  It is now
proved once at the general differential-field layer and the specialized duplicate has been removed.

## Value to the corpus

The exact-factorization form applies whenever the corpus proves

```text
x = product_(i in S) factor_i.
```

It can discharge repeated factorwise-to-product DA obligations and, contrapositively, identify a
necessary HT source in:

- finite one-loop determinants and finite quantum-sector partition functions;
- finite products of special-function observables;
- finite genomic or biochemical multiplicative readouts;
- finite products produced by symbolic regression or expression-learning systems;
- completed arithmetic factorizations represented inside a differential field.

This is strictly stronger as project infrastructure than a theorem tied to one physical model.

## Clock interpretation

A finite product is an observation map applied to finitely many source clocks.  The theorem says
that observation cannot create HT when every clock is DA.  Thus HT belongs to the observable source
structure, not to an implicit time evolution assigned to the product.

## RH pressure test

The theorem is not an RH criterion.  It can localize an HT source in a completed factorization, but
it gives no zero orientation, positivity, or critical-line confinement.  Its RHTower value is
diagnostic: any proposed finite-factor HT mechanism must name an HT factor rather than attribute HT
to completion or multiplication itself.

## Verification

The exact target
`+GaloisForLFunctions.HTGeometry.ClockPeriodCommensurabilityBoundary` refreshed the generalized
dependency.  Direct Lean checks passed for `FiniteDifferentialCircuitBoundary.lean`,
`ClockPeriodCommensurabilityBoundary.lean`, and the existing consumer
`MeromorphicGammaReflection.lean`.  The new declarations depend only on the standard logical
axioms `propext`, `Classical.choice`, and `Quot.sound`.
