# An explicit observable Mayer scattering state

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–3.
- **Input:** [primitive-cone response](gauss-mayer-primitive-cone-scattering-divisor.md).

## Statements

There is an explicit actual Mayer disc-algebra state `H_w`, holomorphic in
the uniform norm for `Re w>0`, `w≠2`, with

```text
H_w(z) = ζ(w)(1+(1+z)^(−w)) + 2 Σ_(0<p<q) (pz+q)^(−w)   (Re w>2),
(I−L_w)H_w = ζ(w)1                                      (w≠1,2),
H_w(0) = 2ζ(w−1)                                        (w≠2).
```

The sum has no coprimality restriction and converges in the actual disc
norm. In the absolute chamber, `H_w=ζ(w)G_w` for the primitive response.
For every `0<Re w<1` with `ζ(w)=0`,

```text
R(w)H_w = H_w,             H_w(0) ≠ 0.
```

Thus the eigenfunction is explicitly constructed and observable at zero.
No assumption of invertibility, simplicity, or boundary observability is
needed at the zero.

## Construction and proof

For `a=1+z`, use the kernel

```text
K(t,a) = (exp(−t)+exp(−at))/((1−exp(−t))(1−exp(−at))).
```

Its expansion is `2/(at²)+O(1)`: the simple singular term cancels.
Subtract `2/(at²)` on `(0,1]`, retain the exponentially decaying tail,
and add `2/(a(w−2))` before dividing by `Γ(w)`. Uniform estimates for
`a∈closedBall(2,3/2)` prove convergence and holomorphy in the disc norm.

Euclidean division partitions the full cone into branch images
`(q,nq+p)` and multiple rays `(a,an)`, `n≥2`. The latter contribute
`ζ(w)(L_w 1−(1+z)^(−w))`. Together with the successor response, this
gives the displayed forcing equation in `Re w>2`. Invertibility there
identifies the lattice response with `ζ(w)G_w` and fixes its value at zero.

For real positive `a`, `K` is the sum of the Barnes kernels with periods
`(a,1)` and initial points `1,a`. Their boundary rays contribute
`ζ(w)(1+a^(−w))`; the strict cone occurs twice. This identifies the Mellin
state with the lattice response on the real diameter. The holomorphic
identity theorem and continuity extend equality to the closed disc.

Fill `C(w)=(w−2)H_w` using its explicit Mellin expression, and fill
`Z(w)=(w−1)ζ(w)` at one. Both are holomorphic on the right half-plane.
The absolute-chamber identities

```text
(w−1)(C−R_w C) − Z(w)P C = (w−2)Z(w)1,
C(w)(0) = 2Z(w−1)
```

therefore continue throughout that connected half-plane. Dividing away
the scalar poles gives the stated formulas. At a strip zeta zero,
`L_w=R_w`, while `ζ(w−1)≠0`; the same state is the required observable
eigenfunction.

## Lean certificates

All modules are in `RenormalizedIntersectionTheory`.

- `GaussMayerScatteringKernel`: exact singular decomposition and uniform head/tail estimates.
- `GaussMayerScatteringMellin`: actual Banach-valued integrals, evaluation, `analyticAt_state`.
- `GaussMayerLatticeRenewal`: `rectangleEquiv`, `renewalEquiv`, `multipleNonmultipleEquiv`.
- `GaussMayerLatticeSource`: `cone_forcing`, `response_equation`, `response_eq_green`, `response_zero`.
- `GaussMayerScatteringChamber`: `state_eq_mellinKernel`, `state_apply_real_expanded`.
- `GaussMayerScatteringState`: `state_eq_response`, `clearedForcing_zero`, `state_zero`,
  `state_equation`, `observable_remainder_eigenfunction`.

Classification of the remaining eigenspace and a Hermitian structure
separating cusp and scattering events remain separate obligations.
