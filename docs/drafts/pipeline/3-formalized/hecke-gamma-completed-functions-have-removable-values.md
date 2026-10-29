# Gamma-completed Hecke functions have their removable values

- **ID:** hecke-gamma-completed-functions-have-removable-values
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Completed residues](hecke-completed-theta-residues-cancel.md)
- **Statement:** Every finite-order Hecke character has a meromorphic Gamma-completed continuation agreeing with the actual ideal series on `Re(s)>1`. For nontrivial characters it is entire, including zero and one, and reciprocal Gamma recovers the ordinary global L-function everywhere.

## Proof

The actual finite class-theta sum is an entire regular term minus its
physical and dual zero-mode quotients. For zero parity, with `n=[K:Q]`,
this is `R(s)-(2/n)P(s)/s+(2/n)Q(s)/(s-1)`.

Entire divided differences give the corrected regular part
`R(s)-(2/n)dslope(P,0,s)+(2/n)dslope(Q,1,s)` and constant residues
`Z=-(2/n)P(0)`, `O=(2/n)Q(1)`. Define the completed function as this
regular part plus `Z/s+O/(s-1)`. Nonzero parity has no zero modes.
This agrees with the actual theta expression away from zero and one and
therefore with Gamma times the ideal series on the initial half-plane.

Both residues vanish for every nontrivial character by the actual raw
residue cancellation theorem. The corrected function is consequently
entire. For the trivial character, its coefficient at one is the positive
ordinary Hecke density times the nonvanishing Gamma value there.

Multiplication by the entire reciprocal Gamma function agrees with the
ordinary L-function on `Re(s)>1`. Analytic uniqueness on the connected
complex plane identifies the two entire functions everywhere, including
all removable values. Defining the completion directly by totalized
Gamma multiplication would not supply these values.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeGammaCompletedFunctionsHaveRemovableValues`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeCompletedThetaRegularPart`
- `heckeCompletedThetaContinuation_eq_regular_sub_poles`
- `heckeGammaCompletedRegularPart`
- `heckeGammaCompletedZeroCoefficient`, `heckeGammaCompletedOneCoefficient`
- `heckeGammaCompletedLFunction`
- `differentiable_heckeGammaCompletedRegularPart`
- `heckeGammaCompletedLFunction_eq_theta`, `heckeGammaCompletedLFunction_eq`
- `meromorphic_heckeGammaCompletedLFunction`
- `heckeGammaCompletedZeroCoefficient_eq_zero`
- `heckeGammaCompletedOneCoefficient_eq_zero`
- `differentiable_heckeGammaCompletedLFunction`
- `heckeGammaCompletedOneCoefficient_eq_pole_mul_gamma`
- `heckeGammaCompletedOneCoefficient_one`
- `heckeGammaCompletedLFunction_mul_gamma_inv`

Both main transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeGammaCompletedFunctionsHaveRemovableValues.lean
```

Wired into the Hecke umbrella without compiling it. [Arithmetic scalar normalization](hecke-completion-factors-have-exact-arithmetic-normalization.md)
and [primitive reflection](primitive-hecke-l-functions-have-completed-functional-equation.md)
are also finalized.
