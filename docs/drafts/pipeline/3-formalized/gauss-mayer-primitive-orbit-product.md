# Primitive-orbit Euler product of the actual Mayer determinant

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parents:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md), [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md).
- **Inputs:** [primitive-orbit logarithm](gauss-mayer-primitive-orbit-logarithm.md), [primitive modular coding](gauss-mayer-modular-primitive-coding.md).

## Statement

For primitive digit-pair cycles `c`, let `ℓ(c)>0` and `λ_c>1` be the
certified pair length and actual expanding multiplier. Then

```text
D(w,z)D(w,−z) = ∏_c ∏_(m≥0) (1−z^(2ℓ(c)) λ_c^(−w−2m)).
```

For each `Re w>1`, this holds on some neighborhood of `z=0`. For
`Re w>2`, it holds throughout `|z|≤1`, including `z=1`. The joint product
over `(c,m)` converges to the same value, and the sum of absolute deviations
of its factors from one is finite.

## Proof

Fix a point in either stated domain, shrinking the local neighborhood so
that `|z|≤1`. Put

```text
a_c = z^(2ℓ(c)) λ_c^(−w),
q_c = λ_c⁻² ∈ (0,1),
x_(c,m) = a_c q_c^m.
```

Positive real bases have no logarithm branch ambiguity. Thus the certified
repetition summand is `T_(c,r)=a_c^r/[r(1−q_c^r)]` for `r≥1`, and
`x_(c,m)=z^(2ℓ(c))λ_c^(−w−2m)`. The source theorem proves
`Σ_(c,r)|T_(c,r)|<∞` and `D(w,z)D(w,−z)=exp(−J)`, with
`J=Σ_c Σ_(r≥1)T_(c,r)`.

The geometric series, with its positive real denominator, gives both

```text
Σ_(m≥0) x_(c,m)^r/r = T_(c,r),
Σ_(m≥0) |x_(c,m)^r/r| = |T_(c,r)|.
```

The second identity and nonnegative Fubini prove absolute convergence of
the full triple series. Consequently all subsequent interchanges are
justified. Its `r=1` subfamily proves `Σ_(c,m)|x_(c,m)|<∞`.

Writing `σ=Re w>0`, one has
`|x_(c,m)|=|z|^(2ℓ(c))λ_c^(−σ)q_c^m<1`.
Taylor's logarithm formula therefore yields
`Σ_(r≥1)x_(c,m)^r/r=−log(1−x_(c,m))`. Absolute Fubini identifies
`Σ_(c,m)−log(1−x_(c,m))=J`. Exponentiating the convergent sum gives a
convergent joint product with value `exp(−J)`, since
`exp(log(1−x_(c,m)))=1−x_(c,m)` and each factor is nonzero.

For each fixed cycle, its logarithm subseries converges absolutely, so its
mode product exists. Product Fubini identifies the nested cycle/mode
product with the joint product. Substitution of the certified source
determinant identity proves the statement.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerPrimitiveOrbitProduct.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitProduct`.

- `orbitWeight`: literal deviation from one in each Euler factor.
- `exists_signed_determinant_eulerProduct`: local absolute convergence and actual determinant identity for `Re w>1`.
- `signed_determinant_eulerProduct_on_closed_unit`: joint and nested products throughout `|z|≤1` for `Re w>2`.
- `signed_determinant_one_eq_eulerProduct`: specialization at `z=1`.

Direct production check passed without diagnostics. All three transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The
programme umbrella imports the module.

## Scope

Cycles use the existing integral conjugacy and primitive-root classification.
No additional identification with inverse classes is imposed. Geometric
geodesic lengths, the Selberg/scattering normalization, and resonance
exclusion are not conclusions of this theorem.
