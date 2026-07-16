# Primitive root quantum multinomial cancellation in every degree

- **ID:** `root-of-unity-quantum-multinomial`
- **Stage:** 3-formalized
- **Type:** THEOREM / QUANTUM ALGEBRA / GENERALIZED CLIFFORD
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [KNOWN PARENT THEORY]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.QuantumBinomialRootOfUnity`

## The theorem

Let `K` be a characteristic-zero field, let `q` be a primitive `d`th root of unity with `d>0`,
and let `X_1,...,X_r` be endomorphisms satisfying

```text
X_i X_j = q X_j X_i   for i<j.
```

Then

```text
(X_1+...+X_r)^d = X_1^d+...+X_r^d.
```

For scalar weights `c_i`, the exact weighted form is

```text
(sum_i c_i X_i)^d = sum_i c_i^d X_i^d.
```

## Proof

Gaussian coefficients are defined by the product formula.  Primitivity makes every denominator
below order `d` nonzero.  The product formula satisfies quantum Pascal, and the final primitive row
has every interior coefficient equal to zero.  This proves the binary identity.  A head generator
`q`-commutes with the sum of a pairwise ordered tail, so list induction gives the finite
multinomial theorem.  Scalar weights are absorbed by the power law for scalar multiples.

## Significance and novelty gate

The quantum freshman's dream and its finite multinomial extension belong to established
root-of-unity quantum algebra.  This card claims no literature novelty.  Its role is foundational:
it supplies an unconditional all-degree scalar horizon law without hiding a Gaussian-binomial or
representation assumption.

## Physical interpretation gate

Mixed histories cancel algebraically at primitive order, leaving only pure sectors.  This is an
exact finite interference law, not yet a probability, unitarity, locality, or QFT theorem.

## RH impact

The identity is universal and nonselective.  It can construct an arithmetic horizon once a
distinguished coefficient family is supplied, but it cannot select Xi or imply RH by itself.

## Lean verification

The direct touched-file check and narrow build target pass.  Principal declarations are
`quantumChoose_primitive_final_coefficient_zero`,
`quantumBinomial_pow_primitive`,
`quantumMultinomial_list_pow_primitive`,
`quantumMultinomial_fin_pow_primitive`, and
`quantumMultinomial_fin_smul_pow_primitive`.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.
