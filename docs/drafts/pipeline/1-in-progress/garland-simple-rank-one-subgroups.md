# The two actual simple rank-one subgroups

- **Stage:** 1-in-progress
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](garland-loop-eisenstein-over-q.md)
- **Target:** Construct injective homomorphisms from `SL₂(F)` for both
  affine simple roots, with exact root and coroot compatibility.

## Dependency and novelty audit

Corpus search found the positive-loop embedding and the actual affine
coroot, but no complete affine `SL₂` embedding. The existing
`laurentTameSymbol_initial_shear` and `laurentTameSymbol_zero_shear` provide
the two zero-entry endpoint identities. Their statements were inspected.
The generic four-elementary-factor theorem and its special-linear matrix
proof are already used and audited by the positive-loop splitting.
This is classical affine Kac–Moody structure, with no novelty claim.

## Dependency-closed paper proof

The finite subgroup is the composition of constant power-series matrices
with the proved positive-loop embedding. Its projection is injective, so
the subgroup map is injective. It restricts to the canonical constant
upper and lower root groups and sends `diag(a,a^-1)` to `h₁(a)`.

For the affine subgroup, first construct the matrix embedding

`j([[a,b],[c,d]]) = [[a,b X^-1],[c X,d]]`.

This is conjugation of the constant matrix by `diag(1,X)` and is an
injective homomorphism. Constants here mean the actual coefficient-field
embedding into the Laurent field.

In the concrete Kubota coordinate model define

`B(g) = d` when `c=0`, and `B(g)=1` when `c!=0`.

The entry `d` is a field unit in the first case by `det(g)=1`.
Equivalently the first branch is the already defined `kubotaUnit(g)`.
Set `J(g)=(j(g),B(g))` with the central coordinate written multiplicatively.

Right multiplication by an upper root preserves `c` and the correction;
its Kubota cocycle is zero. For right multiplication by a lower root with
parameter `s`, put `e=c+ds`. There are four cases:

1. `s=0`: the identity law.
2. `c,e,s` all nonzero: the three lower-left coordinates are `cX,eX,sX`.
   Their cocycle ratios are constants, so their tame pairing is one.
   Both corrections are one.
3. `c=0,s!=0`: then `e=ds!=0`. The tame factor is
   `T(sX,d)=d^-1`, cancelling the old correction `d`.
4. `c!=0,e=0`: then `s,d!=0` and `c=-ds`. The proved zero-shear identity
   gives `T(d/(cX),d/(sX))=d`, because `T(cX,d)=d^-1`.
   This is exactly the new correction at `e=0`.

Thus `J(g u)=J(g)J(u)` for either root group. Every coefficient-field
special-linear matrix is a product of four alternating root elements;
iterating these two identities proves `J(gh)=J(g)J(h)` for all `g,h`.
The matrix projection proves injectivity.

Both root corrections are one, so `J` sends the upper parameter `s` to
the actual upper root at `sX^-1`, and the lower parameter `s` to the actual
lower root at `sX`. On a diagonal, its correction is `a^-1`; hence

`J(diag(a,a^-1)) = z(a^-1) h₁(a) = h₀(a^-1)`.

The reversal of the finite simple-coroot orientation is explicit: the
affine positive root is the lower root at degree one. Conjugation by the
finite Weyl matrix sends upper `s` to lower `-s` and reverses the coroot.
Following this by `sl2Rescale(-1)` removes both root signs. The resulting
coordinate swap is an injective homomorphism, sends upper `s` to lower
`s`, and sends `diag(a,a^-1)` to `diag(a^-1,a)`. Composing `J` with this
swap gives the affine simple embedding with standard positive-root
parameter `sX` and exact coroot `h₀(a)`.

## Scope and status

Paper proof recorded. `SL2DiagonalRescaling`, `ConstantSL2Embedding`,
`AffineSL2Kubota`, `AffineSL2Embedding`, and `SimpleRankOneEmbeddings` are
written, including both
subgroup maps, the exact central correction, elementary multiplication,
full homomorphism law, injectivity, and root/coroot restrictions.
`SL2DiagonalRescaling` and `ConstantSL2Embedding` passed their dependency
builds cleanly. `AffineSL2Kubota` also passed cleanly, including the exact
correction on all lower-root cases. `AffineSL2Embedding` and
`SimpleRankOneEmbeddings` also passed cleanly. All five modules are wired
into the umbrella. Final direct source checks passed for
`SL2DiagonalRescaling` and `ConstantSL2Embedding`; `AffineSL2Kubota` is
being checked. `AffineSL2Embedding`, `SimpleRankOneEmbeddings`, and the
transitive audit remain. The audit scratch is
`/tmp/GarlandRankOneAudit.lean`. Scratch verification
confirmed the field instance of finite maximal spectrum needed for
four-factor generation. The oriented affine simple embedding is written
using Weyl conjugation followed by the sign rescaling. These rank-one
subgroups will support the two simple compact rotation groups over the
reals. They do not by themselves prove global Iwasawa decomposition,
uniqueness of its positive central coordinate, or any arithmetic series.
The next open metric and Iwasawa route is recorded in
[the determinant-metric card](garland-determinant-metric-iwasawa.md).
