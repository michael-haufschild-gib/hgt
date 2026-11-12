# The geometric involutions and their fixed fields

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Location of conjugation; complete-fibre ground field.

Write `w_q=t_q+iδ_q`, with complete-fibre source field `K`. Put
`L=ℚ(all w)`, `M=L(i)`, `F=K(all δ_q)`, and `E=K(all δ_qδ_r)`.
The [Gaussian obstruction](galois-zero-gaussian-extension.md) proves that
functional-equation reflection lifts to `Gal(M/K)` exactly when `i∉L`.

## Theorem

Whenever that lift exists, denote it by `ι`, ordinary conjugation by `c`,
and their product by `ν=cι`. On every original zero, `ι(ρ)=1−ρ` and
`ν(ρ)=1−conj(ρ)`. The fixed fields are

```
M^c = F,       M^ι = L,       M^ν = E(i),       M^{c,ι} = E.
```

The actions are central. An explicit homomorphism
`C₂×C₂ → Gal(M/K)` sends the three nonidentity signs to `ι`, `c`, and `ν`.
It is injective whenever a width is nonzero. If all widths vanish,
`ν=id` and `c=ι`. The [biquadratic diagram](galois-zero-biquadratic-diagram.md)
identifies the three distinct quadratic fields in the faithful regime.

## Proof

The established equivalence `Gal(M/K) ≅ Gal(L/K)×C₂` sends `ι` to
`(id,−1)` and `c` to `(c_L,−1)`. Thus `ν` has coordinates `(c_L,1)`.
Centrality of `c_L` proves centrality of all three actions. A nonzero width
makes `c_L` nontrivial, so the two sign coordinates act faithfully.

Write `z=a+ib`, with `a,b∈L`. Functional reflection sends it to `a−ib`,
so its fixed field is `L`. Line reflection sends it to
`conj(a)+i conj(b)`. Equality with `z` forces both coefficients real;
they lie in `L∩ℝ=E`, giving fixed field `E(i)`. The common fixed field
of `c` and `ι` is `L∩ℝ=E`. The established identity `M∩ℝ=F` gives `M^c=F`.

## Formalization

`GaloisTheoryOfZeros/TheGeometricInvolutionsOfTheZeroField.lean` proves the
original-zero actions, centrality, `sourceFunctionalReflection_fixed_iff`,
`sourceLineReflection_fixed_iff`, `source_geometric_common_fixed`,
and the faithful central `sourceGeometricKleinFour` action.
`TheRealWidthFieldOfTheZeros.realWidthField_comap_eq_fixedField` supplies
ordinary conjugation's fixed field.

Direct source audit passed with `lake --old env lean`. Seven main dependency
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import wired. These classifications do not decide the actual
Gaussian regime or purity.
