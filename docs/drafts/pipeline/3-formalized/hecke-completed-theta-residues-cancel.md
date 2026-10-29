# Completed Hecke theta residues cancel for nontrivial characters

- **ID:** hecke-completed-theta-residues-cancel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Completed residue cancellation](../1-in-progress/hecke-unramified-character-descent-and-residue-cancellation.md)
- **Statement:** Both raw completed-theta zero-mode numerators vanish at their polar points for every nontrivial finite-order Hecke character, before multiplication by reciprocal Gamma.

## Proof

Both numerators are finite sums of entire inverse-class weights times
constant zero-mode factors. For zero real parity and trivial finite
weight, the actual character descends to an ordinary-class character
`phi`. Each base ideal has class `c^-1`, so its value is `phi(c^-1)` and
its inverse weight at zero is `phi(c)`. The descended character is
nontrivial; orthogonality cancels the physical numerator. If finite
weight or parity prevents this descent case, the physical zero mode
vanishes directly.

The ordinary dual numerator is the raw completed dual numerator times
reciprocal Gamma. Its residue is `(2/[K:Q])` times its value at one and
is already proved zero for every nontrivial character. Positive field
degree and nonvanishing Gamma at one therefore cancel the raw completed
dual numerator. For nonzero parity, the dual zero mode vanishes directly.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeCompletedThetaResiduesCancel`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeCompletedPhysicalNumerator`, `heckeCompletedDualNumerator`
- `differentiable_heckeCompletedPhysicalNumerator`
- `differentiable_heckeCompletedDualNumerator`
- `heckeClassBaseIdeal_value_of_descent`
- `heckeClassWeight_zero_of_descent`
- `heckeCompletedPhysicalNumerator_zero`
- `heckeGlobalDualNumerator_eq_completed`
- `heckeCompletedDualNumerator_one`

Both cancellation theorems have transitive axioms only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeCompletedThetaResiduesCancel.lean
```

The module is wired into the Hecke umbrella without compiling it. The
divided-difference completion and normalized functional equation remain
separate obligations.
