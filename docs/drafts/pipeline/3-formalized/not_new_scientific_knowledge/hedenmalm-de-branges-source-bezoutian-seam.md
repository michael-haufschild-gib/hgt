# Hedenmalm--de Branges source Bezoutian seam

- **ID:** `hedenmalm-de-branges-source-bezoutian-seam`
- **Stage:** 3-formalized
- **Type:** BRIDGE / SOURCE-DEFINED HILBERT--POLYA KERNEL
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-BEARING POSITIVITY OPEN]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmDeBrangesSeam.lean`

## Unconditional theorem

Let

```text
A(z)=XiC(z),
E(z)=A(z)+i A'(z),
E#(z)=A(z)-i A'(z).
```

These functions are constructed from the completed theta transform and its first moment; their
definition contains no Xi zero. Their division-free commutator is

```text
E(z)E#(v)-E#(z)E(v)
  =2i(A'(z)A(v)-A(z)A'(v)).                              (1)
```

Define the removable Bezoutian on the diagonal by

```text
B_A(z,v)
 =dslope(v |-> A'(z)A(v)-A(z)A'(v),z,v).                 (2)
```

Then globally

```text
E(z)E#(v)-E#(z)E(v)=2i(v-z)B_A(z,v),                     (3)
```

and

```text
B_A(z,z)=A'(z)^2-A(z)A''(z).                             (4)
```

Consequently, at Xi zeros `alpha` and `beta`,

```text
B_A(alpha,alpha)=A'(alpha)^2,                            (5)
B_A(alpha,beta)=0                 if alpha!=beta.         (6)
```

At an actual divisor support point,

```text
B_A(alpha,alpha)!=0
  iff the analytic multiplicity at alpha is one.         (7)
```

Thus the Hedenmalm divided quotient and the de Branges kernel have the same exact local defect:
they retain a simple divisor fiber and lose the first level at a multiple zero.

## Hilbert--Polya reading

The kernel is source-defined before positivity. If its anti-holomorphic specialization is positive
on the critical half-plane, the usual de Branges construction supplies a positive reproducing-
kernel Hilbert space in which distinct simple Xi zeros give orthogonal kernel vectors. The missing
statement is therefore not the construction of another divisor-indexed diagonal operator. It is
the source inequality which makes `(2)` positive.

This also shows that the Hedenmalm and de Branges routes are not independent at their terminal
metric layer. Their common source object is the Xi derivative Bezoutian. Any proposed Hedenmalm
metric which reaches this kernel has reached the classical de Branges/Weil positivity boundary.

The companion pointed-moment seam removes one possible ambiguity. The normalized continued
prime--archimedean moment germ `G` has the exact odd lift `T(z)=-zG(z)` to the distinguished
Euler--Gamma trace, and its complete analytic Taylor jet determines that germ locally. The source
differential identity then gives

```text
E(z)=XiC(z)(1-i zG(z)),
B_A(z,v)=XiC(z)XiC(v)(vG(v)-zG(z))/(v-z)
```

near the center and off the diagonal. Thus the current route is not using an unpointed formal
moment sequence. Its analytic lift is determinate, and the central normalization makes `XiC` the
unique entire solution of the induced first-order source constraint; the unresolved statement is still global
positive orientation of the kernel.

## Parent-theory collision and score

Equations `(1)`--`(6)` are the classical Hermite--Biehler/de Branges Bezoutian algebra specialized
to the completed theta transform. Equation `(7)` is ordinary analytic multiplicity detection by
the first derivative. The specialization is useful because it removes a target-fed operator from
the route and identifies the exact source kernel, but it introduces no new positivity mechanism.

Honest score: **45/100**. This is rigorous route consolidation, not publishable new scientific
knowledge. It will matter only if the theta/all-prime source yields a non-target-fed Gram
factorization of `B_A`.

## Formal theorem surface

- `xiHedenmalmDeBrangesE`;
- `xiHedenmalmDeBrangesESharp`;
- `xiHedenmalm_XiC_conj`;
- `deriv_XiC_conj`;
- `xiWeilSharp_xiHedenmalmDeBrangesE`;
- `xiHedenmalmDeBrangesCommutator_eq`;
- `xiHedenmalmDeBrangesCommutator_eq_mul_bezoutian`;
- `xiHedenmalmBezoutian_eq_div`;
- `xiHedenmalmBezoutian_self`;
- `xiHedenmalmBezoutian_self_of_zero`;
- `xiHedenmalmBezoutian_eq_zero_of_distinct_zeros`;
- `xiHedenmalmBezoutian_self_ne_zero_iff_simple`.

The exact module build passes. The headline declarations use only the standard Lean foundations
`propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or placeholder
hypotheses.

## Gates

- [x] source-defined Hermite--Biehler candidate
- [x] exact division-free commutator identity
- [x] removable diagonal Bezoutian
- [x] exact diagonal and distinct-zero values
- [x] multiplicity-one criterion
- [x] exact build and axiom audit
- [x] classified as a standard bridge
- [x] pointed analytic-moment determinacy and local source reconstruction
- [ ] source Gram factorization of the critical Bezoutian
- [ ] positivity without divisor input
- [ ] RH
