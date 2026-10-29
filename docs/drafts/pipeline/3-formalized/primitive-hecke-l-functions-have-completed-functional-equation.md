# Primitive Hecke L-functions satisfy the completed functional equation

- **ID:** primitive-hecke-l-functions-have-completed-functional-equation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual averaged Mellin identity](hecke-dual-averaged-mellin-is-the-inverse-class-series.md), [arithmetic normalization](hecke-completion-factors-have-exact-arithmetic-normalization.md), [completed removable values](hecke-gamma-completed-functions-have-removable-values.md)
- **Statement:** For every finite-primitive finite-order Hecke character, the actual discriminant/conductor-completed L-function satisfies reflection with its arithmetic unit root number. The equation holds off the two possible poles, everywhere after clearing them, and at every complex point for nontrivial characters.

## Proof

The actual dual fractional ideal for a class base `b` is `dual(mb)`.
Its inverse class is the fixed conductor/codifferent class shift times
`[b]`. Since the chosen base for `c` has class `c^-1`, this gives the
explicit permutation `c ↦ [dual(m)]^-1 c^-1` of ordinary ideal classes.
Reindexing by this permutation identifies the sum of actual dual class
series with the complete inverse-character Hecke series.

For `Re(s)>1`, actual theta reflection and the proved absolutely
convergent dual Mellin formula identify the reflected completed-theta
sum. The exact normalization theorem cancels the base character, base
norm, torsion order, and logarithmic Jacobian. Multiplying by
`delta^((1-s)/2)`, where `delta=|disc K|Norm(m)`, leaves

```
Lambda_psi(1-s) = W_psi Lambda_(psi^-1)(s),
W_psi = (C_psi / sqrt(Norm(m))) (-i)^d,
||W_psi|| = 1.
```

The completed function uses the already constructed entire regular part
and constant residues `Z` and `O`. Define its entire pole-cleared form
before totalized division:

```
Xi_psi(s) = delta^(s/2) *
  (s(s-1) Regular_psi(s) + (s-1) Z_psi + s O_psi).
```

Away from zero and one, this equals `s(s-1)Lambda_psi(s)`. The identity
principle extends its half-plane reflection to every complex point.
Cancelling `s(s-1)` gives completed reflection away from the possible
poles. For a nontrivial character, both residues vanish and the actual
completion is entire. Its inverse character is also nontrivial, so the
identity principle gives completed reflection at every point, including
both removable values. No analytic or arithmetic input is assumed.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.PrimitiveHeckeLFunctionsHaveCompletedFunctionalEquation`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualClassL_eq_permuted_inverseClassL`
- `heckeL_inverse_eq_sum_dualClassL`
- `heckeCompletedThetaContinuation_one_sub`
- `heckeCompletedLFunction`, `heckeCompletedLFunction_eq`
- `meromorphic_heckeCompletedLFunction`
- `differentiable_heckeCompletedLFunction`
- `heckeCompletedLFunction_reflection_right`
- `heckePoleClearedCompletion`, `differentiable_heckePoleClearedCompletion`
- `heckePoleClearedCompletion_eq`
- `heckePoleClearedCompletion_reflection`
- `heckeCompletedLFunction_reflection`
- `heckeCompletedLFunction_reflection_entire`

The class recombination, global pole-cleared reflection, and entire
nontrivial-character reflection audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/PrimitiveHeckeLFunctionsHaveCompletedFunctionalEquation.lean
```

Wired into the Hecke umbrella without compiling it. No consumer olean is
needed. This closes HL7; the larger programme remains paused before CFT.
