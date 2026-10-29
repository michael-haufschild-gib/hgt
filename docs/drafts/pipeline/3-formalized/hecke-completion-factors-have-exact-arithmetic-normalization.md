# Hecke completion factors have exact arithmetic normalization

- **ID:** hecke-completion-factors-have-exact-arithmetic-normalization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual class Mellin integrals](hecke-dual-class-kernels-have-exact-mellin-integrals.md)
- **Statement:** The actual reflected class-theta factors cancel every base-ideal dependence and yield the standard discriminant/conductor completion with an arithmetic root number of absolute value one for primitive characters.

## Proof

Write `D=|disc K|`, `N=Norm(m)`, `B=Norm(b)`, `delta=D*N`, and let
`d` be the real parity degree. The actual trace-dual norm is
`Norm(dual(mb))=(delta*B)^-1`. Positive-real complex-power identities
therefore express the dual Mellin factor as `Cψ ψ(b) delta^s B^s`.
The actual Poisson scalar at zero profile is `(-i)^d/(N B sqrt(D))`.

The reflected class weight is `ψ(b)^-1 B^(1-s)`. Its character cancels
the dual character factor, and `B^(1-s)B^s=B` cancels the base norm.
Every class summand consequently has the same scalar

```
Cψ (-i)^d delta^s / (N sqrt(D)).
```

Define the entire nonvanishing completion factor `delta^(s/2)` and
`Wψ=(Cψ/sqrt(N))(-i)^d`. Complex-power addition and
`sqrt(delta)/(N sqrt(D))=1/sqrt(N)` prove that multiplying the common
scalar by `delta^((1-s)/2)` gives `Wψ delta^(s/2)`. The previously proved
primitive Gauss norm and unit modulus of the parity phase give `||Wψ||=1`.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeCompletionFactorsHaveExactArithmeticNormalization`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeCompletionNorm`, `heckeCompletionNorm_pos`
- `heckeCompletionFactor`, `differentiable_heckeCompletionFactor`
- `heckeCompletionFactor_ne_zero`
- `heckeRootNumber`, `norm_heckeRootNumber`
- `heckeDualMellinFactor_eq_completionNorm`
- `heckeThetaMellinScalar_zero_eq`
- `heckeClassWeight_mul_reflectedDualFactor`
- `heckeCompletionFactor_mul_reflectionScalar`

All three main transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeCompletionFactorsHaveExactArithmeticNormalization.lean
```

Wired into the Hecke umbrella without compiling it. Finite class
recombination and global reflection are finalized in
[the completed functional equation](primitive-hecke-l-functions-have-completed-functional-equation.md).
