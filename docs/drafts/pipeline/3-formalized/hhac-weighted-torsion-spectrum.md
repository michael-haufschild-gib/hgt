# Spectrum of the weighted torsion limit

- **ID:** hhac-weighted-torsion-spectrum
- **Stage:** 3-formalized
- **Type:** SPECTRAL CLASSIFICATION
- **Status:** Complete classification formalized

## Exact classification

For every `δ>0`, the actual torsion-limit form on `Hδ=ℓ²(n^δ)` represents a
compact self-adjoint operator. Both positive and negative definite subspaces
have arbitrarily large finite dimension. Every finite family of linear
constraints leaves both signs; every bilinear correction through a
finite-dimensional space leaves the form indefinite.

The Hilbert–Schmidt threshold is exactly `δ>1/2`. Above it the squared norm is

`2(Σ_(m≥1) m^(−2δ))(Σ_(t≥1) Λ(t)²/t^(1+δ)) + Σ_(n≥1) d(n)²/n^(2δ)`.

Here `d(n)` is the original tame different and `Λ(1)=0`. These statements
concern the actual torsion kernel, not its gcd majorant or a model matrix.

## Proof

For `0<β<δ`, coefficient-preserving inclusion `J:Hδ→Hβ` multiplies normalized
coordinates by `n^((β−δ)/2)`. Its finite-rank truncations converge in norm.
The original absolutely convergent pair series gives
`Lδ(u,v)=Lβ(Ju,Jv)`. Compactness follows, and symmetry gives self-adjointness.

On `{q,2q}` for odd prime `q`, the arithmetic matrix is
`[[d(q),−log(2)/√2],[−log(2)/√2,d(q)+log(2)]]`.
Different prime pairs have zero mixed entries. Equal coordinates have energy
`2d(q)−(√2−1)log(2)`, negative eventually; the second coordinate has positive
energy. Orthogonal synthesis gives definite subspaces of every finite dimension.
A map into a fixed finite-dimensional correction space has nonzero kernel on
a sufficiently large such subspace. These are compressions; invariance under
the full operator is not required.

The normalized matrix is `L(m,n)/(mn)^(δ/2)`. Its divisor half is supported
on `(m,mt)`, with square `m^(−2δ)Λ(t)²t^(−1−δ)`. The two strict divisor
halves and the diagonal are disjoint. Nonnegative product summation gives
the displayed exact square mass; logarithmic envelopes prove convergence
for `δ>1/2`. Parseval identifies it with the actual Hilbert–Schmidt norm.
For necessity, `d(2k)≥log 2` makes the even diagonal dominate the divergent
power series whenever `δ≤1/2`.

## Lean declarations

- `weightedProbeInclusion_compact`, `spacingLimitOperator_factor`,
  `spacingLimitHilbertOperator_selfAdjoint`, `spacingLimitHilbertOperator_compact`.
- `SpacingDefiniteFamilies` and `SpacingFiniteConstraints`: actual definite
  synthesis, arbitrary finite constraints and finite-rank correction obstruction.
- `TorsionHilbertSchmidtBoundary`: `spacingNormalizedMatrix_square_tsum`,
  `spacingLimitHilbertOperator_hilbertSchmidt_iff`,
  `spacingLimitHilbertOperator_hsNormSq`.

The direct production Lean check and eighteen transitive axiom audits pass
with only `propext`, `Classical.choice` and `Quot.sound`. Compactness and
finite-rank sign modules also pass their direct checks and axiom audits.

## Positive survivor and prior work

The survivor comprises exact prime-pair compressions, compactness, both
infinite sign indices and the sharp summability boundary with exact norm.
No conclusion about the full Weil form or its archimedean payment follows.

[Hilberdink–Pushnitski](https://arxiv.org/abs/2110.14323) prove compactness and
power eigenvalue asymptotics for LCM matrices `E(σ,τ)_(m,n)=(mn)^σ/lcm(m,n)^τ`.
The substitution `τ=1`, `σ=(1−δ)/2` identifies the positive normalized gcd
majorant with that family. Their [indefinite LCM family](https://arxiv.org/abs/2401.06892)
also has infinitely many eigenvalues of each sign in its stated range.
Neither identifies this variable-diagonal torsion kernel. Existing corpus
constant-counterterm index laws also use a different diagonal. No priority
claim is made for compactness or orthogonal negative-vector arguments.
