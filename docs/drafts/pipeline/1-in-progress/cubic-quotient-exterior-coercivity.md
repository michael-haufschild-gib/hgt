# Exterior coercivity on the cubic quotient

- **ID:** cubic-quotient-exterior-coercivity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [cubic theta residue](cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** There are a compact quotient set `K` and `C≥0` such that every actual energy vector satisfies `‖u‖₂²≤E(u)+C‖1_Ku‖₂²`.

Construct an invariant positive smooth barrier equal to height in every
high cusp. Distinct cusp heights have product at most one. High rows are
locally finite because their four integral coordinates are uniformly
bounded by the inverse matrix. Thus a smooth height profile gives a
locally finite invariant sum. Bianchi reduction confines its Laplacian
defect to a compact quotient set.

For the positive Laplacian, the intended potential is `V=Δφ/φ`, with
`V≥1−C1_K`. Local Green identities and a finite smooth partition should
give `∫V|f|²≤E(f)` by completing the square in `∇f−f∇φ/φ`.
Density then passes the inequality to the completed energy graph.

The local and global Green identities, including equations holding only
on test support, are formalized. Coordinate equations identify the actual
variational operator graph; see [Green identity](../3-formalized/cubic-quotient-green-identity.md).

Open: barrier construction and defect equation, ground-state inequality,
and passage to the completed graph. Compactness
of `1_K` is tracked on [formalized local compactness](../3-formalized/cubic-kernel-local-sobolev-compactness.md).

External argument: OpenAI `Eisenstein/CuspHeight.lean`,
`BarrierPotential.lean`, `MeanSquare/UnitRows.lean`, and
`CubicSieve/CutoffOrders.lean`. The direct bounded-row proof of local
finiteness would reuse the corpus Bianchi reduction instead of the
external spatial derivative majorants.
