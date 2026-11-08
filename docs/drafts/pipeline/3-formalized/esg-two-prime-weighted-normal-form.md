# A filtered two-prime normal form for weighted chains

- **ID:** esg-two-prime-weighted-normal-form
- **Stage:** 3-formalized
- **Type:** FILTERED CHAIN NORMAL FORM

## Exact theorem

Over every commutative ring, the actual prime-valued augmented chain persistence
is naturally isomorphic to the differential supported at vertices two and
three, with coefficients two and three. Both inverse maps preserve every
prime-product cutoff and commute with canonical integral coefficient extension.
The induced comparison retains the actual homology persistence maps.

Bounded core/tag labels give a basis of the original cutoff chain modules.
Height inclusion extends the same coefficients by zero at newly born labels.
For a core of product `m` and cardinality `k`, the four tags have:

| Tag | Exterior degree | Birth |
|---|---:|---:|
| Core | `k` | `m` |
| Two | `k+1` | `2m` |
| Three | `k+1` | `3m` |
| Both | `k+2` | `6m` |

The core atom is closed; the two middle generators have boundary coefficients
`2,3`, and the top generator has boundary `2e₃−3e₂`. These are identities in
the original prime-valued chain complex and its actual transformed basis.

## Proof

Write `d=ιφ`, `t=ιψ`, `h=u∧`, where `φ(e_p)=p`, `u=e₃−e₂`, and `ψ`
agrees with `φ` above three and vanishes at two and three. Cartan's identities
give `dh+hd=1`, `th+ht=0`; Koszul contractions satisfy `t²=0`, `dt+td=0`.
Thus `H=ht` is square-zero, and `F=1−H`, `G=1+H` are inverse. Moreover

`dF=d−t+hdt=(1−ht)(d−t)=F(d−t)`.

In exterior degree zero take `H=0`; the comparison follows from `dh=1`.
A tail deletion removes a prime above three, paying for either small-prime
cone. Both gauges therefore preserve each cutoff. Their ambient formulas
commute with height inclusion and canonical integral coefficient extension.

Transporting the exterior face basis through `F` preserves its exact
cutoff-span description. Removing two and three partitions every face uniquely
into a core and tag; insertion gives the stated cardinalities and products.
Restricting and reindexing the transported basis gives actual cutoff chain
coordinates. The ordered small-prime cones agree with the increasing face
basis, so `dF=F(d−t)` identifies the row `(2,3)` and column `(-3,2)` exactly.

## Lean realization

All modules belong to `EffectiveScalingGeometry` and its umbrella:

- `PrimeTwoPrimeNormalForm`: actual cutoff and persistence isomorphisms,
  including canonical integral coefficient compatibility.
- `PrimeTwoPrimeBlocks`: transformed basis, unchanged cutoff spans and sparse
  arithmetic boundary.
- `PrimeTwoPrimeFaces`: unique core/tag partition, degrees, products and
  bounded-degree bijection.
- `PrimeTwoPrimeBlockCoordinates`: actual block coordinates, natural height
  maps and the exact tagged-vector matrices.

All four modules pass direct `lake --old env lean` audits. Their printed
capstones depend exactly on `[propext, Classical.choice, Quot.sound]`.

## Existing work and boundary

Weighted simplicial persistence is established in
[Ren–Wu–Wu](https://arxiv.org/abs/1708.06722).
[Li–Reidys](https://arxiv.org/abs/2205.03435) and
[Bura–Dutta–Li–Reidys](https://arxiv.org/abs/2206.04612) give structure and
algorithms over discrete valuation rings. No literature-priority claim is
made. The comparison here retains the actual arithmetic cutoffs and maps.

[Arbitrary-coefficient homology](../1-in-progress/esg-all-coefficient-weighted-homology.md)
requires the resulting cycle and boundary quotient comparisons. A chain
normal form alone supplies neither signed Euler cancellation nor an
arithmetic height sign.
