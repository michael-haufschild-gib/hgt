# Exact Mellin integrals of actual dual class kernels

- **ID:** hecke-dual-class-kernels-have-exact-mellin-integrals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual theta unfolding](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** Each selected actual trace-dual class generator has joint Mellin density equal to its inverse Hecke ideal term times one common arithmetic factor and a translated archimedean kernel. Its exact Mellin integral and absolute mass are determined, and the absolute masses are summable on `Re(s)>1`.

## Proof

For `J=dual(mb)` and the selected generator `(g_I)=I J`, the proved
arithmetic identities give

```
F_b(g_I) sgnψ(g_I) = Cψ ψ(b) ψ⁻¹(I),
|Norm(g_I)| = Norm(I) Norm(J).
```

Complex powers multiply on nonnegative real arguments. Therefore the
sign/norm coefficient is the actual inverse ideal term times

```
A_b(s) = Cψ ψ(b) Norm(J)^(-s).
```

The proved arbitrary-field-element Mellin identity now separates the
joint density into `idealTerm(ψ⁻¹,s,I) A_b(s)` times a translated place
kernel. Translation invariance gives joint absolute integrability on
`Re(s)>0`, and

```
2 integral_joint density_I
  = idealTerm(ψ⁻¹,s,I) A_b(s) Γψ(s)/(degree * 2^unitRank).
```

Its absolute mass is the ideal-term norm times `||A_b(s)||` times one
common archimedean mass. Absolute convergence of the actual inverse
Hecke ideal series proves summability of these masses for `Re(s)>1`.
No bound or coefficient identity is assumed separately.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeDualClassKernelsHaveExactMellinIntegrals`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualMellinFactor`
- `heckeDualClassFrequency_mellinCoefficient`
- `heckeDualClassLogMellinKernel`, `heckeDualClassLogMellinKernel_eq`
- `integrable_heckeDualClassLogMellinKernel`
- `integral_norm_heckeDualClassLogMellinKernel`
- `summable_integral_norm_heckeDualClassLogMellinKernel`
- `integral_heckeDualClassLogMellinKernel`

All four main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeDualClassKernelsHaveExactMellinIntegrals.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
Actual averaged-dual-theta unfolding and its infinite Mellin exchange
remain separate obligations.
