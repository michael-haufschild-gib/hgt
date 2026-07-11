# Rayleigh-gap projective transfer

- **ID:** `rayleigh-gap-projective-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** For a unit eigenvector `v` of a symmetric operator at energy `epsilon`, a positive
  shifted-form gap on the component of a unit source `g` orthogonal to `v` gives

  ```text
  1-||inner(v,g)||^2
    <=(Rayleigh(g)-epsilon)/gap.
  ```

## Role in the RH chain

The theorem consumes exactly the quantitative source hypothesis isolated by the CCM route:

```text
source-specific true-Weil Rayleigh excess / true even gap -> 0.
```

Its conclusion is projective convergence of the source to the true ground eigendirection. It
contains no `Xi`, zeta-zero, zero-location, or RH predicate and remains independently falsifiable
for any symmetric operator and proposed source.

The downstream chain is now separated as

```text
renormalized radial/archimedean source estimate
  + true even coercive gap
  -> projective ground-vector convergence                 [Lean, this card]
  -> growing Mellin convergence
  -> locally uniform Hermitian determinant convergence
  -> RH.                                                  [Lean, existing]
```

## Formal declarations

The module `GaloisForLFunctions.RHTower.RayleighGapProjective` proves:

```text
unitProjectiveRemainder_inner_eq_zero
norm_projectiveRemainder_sq
shiftedForm_projectiveDecomposition
projectiveRemainder_sq_le_rayleighExcess_div_gap
one_sub_norm_inner_sq_le_rayleighExcess_div_gap
```

The coercivity hypothesis is the source-pure form of the true even spectral gap. No finite-
dimensional eigenvalue enumeration or RH-strength positivity assumption is hidden in the theorem.

## Gates

- [x] orthogonal projective remainder formalized
- [x] projective defect identity formalized
- [x] shifted eigenform decomposition formalized
- [x] Rayleigh-excess/gap estimate formalized
- [x] producing target builds and axiom audit passes
- [ ] instantiate the theorem with the true restricted Weil operator
- [ ] formalize the growing Mellin evaluation bound
