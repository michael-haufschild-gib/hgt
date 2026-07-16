# Joint source-realization common-kernel criterion

- **ID:** `joint-source-realization-common-kernel-criterion`
- **Stage:** 3-formalized
- **Type:** EXACT RECONSTRUCTION CRITERION / JOINT-CONSERVATIVITY GATE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/JointSourceRealizationConservativity.lean`
- **Parent:**
  `../../1-in-progress/hypertranscendental-constraint-hodge-duality.md`

## Theorem

Let `S` be a commuting difference-differential field with source indices `i`, and let

```text
R_r:K -> A,   r in rho,
```

be an arbitrary labelled family of additive realization maps.  Define

```text
Obs_R(x)=((sigma_i-1)x)_i  x  (R_r(x))_r.                 (1)
```

Then

```text
Obs_R(x)=Obs_R(y)
  iff x-y is fixed by every sigma_i
      and R_r(x-y)=0 for every r.                         (2)
```

Consequently

```text
Obs_R is injective
  iff intersection_r ker(R_r) intersection K^S = {0}.    (3)
```

If a nonzero `z` lies in the intersection in `(3)`, the pair `z,0` is an explicit
nonconservativity witness.  Thus a family of realization maps is not jointly conservative merely
because its values have been placed in one product.  It must kill the actual residual source
gauge.

## Meaning for the five HT realizations

Equation `(3)` is the algebraic gate for the proposed analytic, monodromy, spectral, Hermitian,
and integral realization family.  An application must:

1. construct each realization independently;
2. identify its restriction to the source joint-fixed gauge;
3. prove that the five kernels have trivial intersection there;
4. produce a nonzero common-kernel witness if any channel is deleted and minimality is claimed.

The theorem does not pretend that all five nonlinear realization categories are additive or have
one common codomain.  It is the exact linearized comparison theorem they must recover on tangent,
logarithmic, or abelianized source gauges.  The full typed essential-image theorem remains a
separate obligation.

## Proof

The source-boundary equality is equivalent to joint fixedness of `x-y`.  Equality in the `r`th
realization is equivalent, by additivity, to `R_r(x-y)=0`.  Taking the product gives `(2)`.
Injectivity is precisely the assertion that the only element satisfying those conditions is zero,
which is `(3)`.  The converse witness is immediate. `QED`

## Lean certificate

Declarations:

- `familyRealizedBoundaryFingerprint`;
- `familyRealizedBoundaryFingerprint_eq_iff`;
- `familyRealizedBoundaryFingerprint_injective_iff`;
- `familyRealizedBoundaryFingerprint_not_injective`.

The exact-module build passes.  Axiom inspection reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The declarations contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
declaration.

## Novelty and anti-theatre gate

Kernel-intersection criteria and faithful product functors are parent algebra and category theory.
No novelty is claimed.

- `[ANTI-THEATRE -- PASS]` The criterion is used as a falsifier: an asserted realization package
  must calculate the common kernel, not cite the existence of a product.
- `[NOVELTY -- PARENT]` Formalization and HT terminology do not make `(2)`--`(3)` new mathematics.
- `[SIGNIFICANCE -- LOAD-BEARING BRIDGE]` It gives the exact proof obligation for joint
  conservativity and exposes every residual gauge witness.
- `[RH BOUNDARY]` No zeta source, zero divisor, positivity statement, or RH conclusion occurs.

## Gates

- [x] equality fibre calculated exactly
- [x] joint conservativity characterized by a common kernel
- [x] explicit nonconservativity witness theorem
- [x] Lean-formalized unconditionally
- [x] separated from the nonlinear typed essential-image conjecture
- [ ] instantiate all five nonlinear HT realizations on a second natural source family
