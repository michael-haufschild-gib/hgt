# Finite-field orientation counts

- **ID:** RIAC-finite-field-orientation-counts
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical arithmetic calibration
- **Source:** [discriminant-cover construction](riac-discriminant-cover-signed-counts.md)
- **Statement:** Residue-field trace discriminants define actual finite covers whose signed fibre counts recover polynomial Möbius signs and cancel exactly in every degree at least two.

## Construction and proof

Let `F` have odd cardinality `q`. For a finite extension `K/F` of degree `d`
and any basis `b`, Frobenius has minimal polynomial `X^d−1`. Equal degrees
identify its characteristic polynomial, so its determinant is `(-1)^(d+1)`.

The embedding matrix `V` of `b` satisfies `V^(q)=AᵀV`, where `A` is the
Frobenius matrix and the left power is entrywise. Its determinant `v` is
nonzero and satisfies `v^q=det(A)v`; also `v²=disc(b)`. Euler's criterion
therefore gives `χ(disc(b))=(-1)^(d+1)`. The actual fibre
`{y∈F:y²=disc(b)}` has `1+(-1)^(d+1)` points.

For each monic irreducible `P`, use the power basis of the actual residue
field `F[X]/(P)`. For a squarefree monic `f`, let `D(f)` be the product of
these trace discriminants over its irreducible factors. Extend `D` by zero
off the squarefree locus. Neither this definition nor its square-root
fibres uses the Möbius function. Degree additivity and multiplicativity of
`χ` prove `χ(D(f))=(-1)^deg(f) μ(f)`.

Define the finite set

`C_n={(f,y): f monic, deg(f)=n, y∈F, y²=D(f)}`.

Fibre counting gives `#C_n=q^n+(-1)^n Σ_(deg f=n) μ(f)`. The existing,
unconditionally derived polynomial Möbius degree sums yield
`#C_0=2`, `#C_1=2q`, and `#C_n=q^n` for every `n≥2`.

## Exact scope

`D(f)` uses residue-field normalization data. The
[cross-resultant comparison](riac-discriminant-cover-signed-counts.md)
identifies its actual fibres with those of `Polynomial.discr f`, including
ramification. It supplies an independent aggregate count and recovers
polynomial Möbius cancellation from the root-orbit counts. The integral
coefficient equation belongs to the polynomial-discriminant cover.

This is a calibration for the governing integer target
`Σ_p index_p(N)=1−M(N)=Oε(N^(1/2+ε))`. No compatible integer cutoff family,
Frobenius action or square-root estimate is supplied.

## Formalization

[FiniteFieldOrientationCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FiniteFieldOrientationCounts.lean):

- `finiteField_frobenius_charpoly`, `finiteField_frobenius_det`.
- `finiteField_discr_euler`, `finiteField_discr_quadraticChar`.
- `finiteFieldOrientationCover_card`.
- `irreducibleTraceDiscriminant_character`.
- `factorTraceDiscriminant_character`.
- `factorOrientationCover_card_signed`, `factorOrientationCover_card`.

Direct leaf check and nine transitive axiom audits; only `propext`,
`Classical.choice`, `Quot.sound`. No umbrella build.

## Literature boundary

The discriminant orientation mechanism is classical Pellet–Stickelberger
arithmetic; [Afshar, §§1–2](https://arxiv.org/html/2001.05641v1) gives the
Frobenius proof. The contribution here is the formal construction and
comparison of actual residue-field fibres and their aggregate count.
The scalar polynomial Möbius cancellation is reused from
`ArithmeticGaugeTheory.TheFunctionFieldCalibrationIsDerived`.
