# Exposed-face constraint-capacity law

- **ID:** `exposed-face-constraint-capacity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / GENERAL HT BOUNDARY GEOMETRY
- **Scientific status:** `[PROVED FINITE CORE] [FORMALIZATION IN PROGRESS] [NOVELTY UNVERIFIED]`
- **Statement:** The coefficient-relation rank visible on a finite exposed source face is bounded
  by the face cardinality.  Consequently any cofinal zero-temperature boundary that remains
  faithful to coefficient palettes of unbounded rank must have unbounded exposed degeneracy and
  vanishing Renyi-2 purity.

## Finite theorem

Let `J` and `P` be finite, let `c_j(p)` be a complex coefficient packet, and let `E_p` be a real
source marking with upper radius `R`.  Put

```text
P_R={p:E_p=R},
g_R=|P_R|,
C_R=(c_j(p))_(p in P_R,j in J),
r_R=rank(C_R).
```

Then

```text
0 <= r_R <= min(|J|,g_R).                                  (1)
```

If the exposed Gram form

```text
G_R(q)=sum_(p in P_R) a_p |sum_j q_j c_j(p)|^2,  a_p>0,    (2)
```

is nondegenerate, then the restriction map `q -> C_R q` is injective, hence

```text
|J| <= g_R.                                                 (3)
```

For the Gibbs marking `H_p=-E_p`, the zero-temperature purity tends to `1/g_R`.  Therefore
nondegeneracy of an `m`-dimensional coefficient palette forces

```text
lim_(beta->infinity) purity_beta = 1/g_R <= 1/m.            (4)
```

The quantity

```text
v_R=r_R/g_R in [0,1]                                       (5)
```

is the exposed visibility fraction; `g_R-r_R` is the dark exposed degeneracy.  The numerator
records coefficient-relation capacity, while the denominator is independently recovered from
the purity limit.

## Cofinal consequence

Let finite apertures carry coefficient palettes of dimensions `m_N -> infinity`.  If every
exposed boundary form remains nondegenerate on its palette, then `(3)` gives

```text
g_N -> infinity,
1/g_N -> 0.                                                 (6)
```

Thus a cofinal boundary faithful to arbitrarily large HT constraint palettes must have unbounded
exposed degeneracy.  Concentration onto a fixed finite face has uniformly bounded relation rank
and cannot carry universal finite constraint completeness.

## Product target

For tensor coefficient packets and additive source markings, the exposed face is the Cartesian
product.  The target strengthening is

```text
g_(A tensor B)=g_A g_B,
r_(A tensor B)=r_A r_B,
v_(A tensor B)=v_A v_B,                                    (7)
```

and hence

```text
dark_(A tensor B)=dark_A g_B+r_A dark_B.                    (8)
```

The face-cardinality product and normalized Gibbs tensor laws are already formalized.  The matrix
rank product and its composition with `(5)` remain to be added.

## HT significance

The law separates two boundary data that the existing theory had treated independently:

1. purity determines how many source atoms survive;
2. the exposed Gram radical determines which coefficient constraints survive.

Their combination gives a capacity theorem.  A boundary may have large degeneracy but small
constraint rank because many surviving atoms are coefficient-dark.  Conversely, universal HT
constraint visibility forces cofinally growing exposed faces and excludes every fixed-rank
boundary selection mechanism.

## RH audit

For an RH-facing energy marking, the law supplies a route constraint rather than an RH criterion.
Any cofinal cooling construction that claims to retain an unbounded family of zero-separating or
prime-separating constraints must prove unbounded exposed degeneracy and rule out coefficient-dark
mass.  A rank-one or fixed-rank limiting face cannot carry enough information to determine the Xi
divisor.  No conclusion about RH follows from degeneracy or purity alone.

## Dual gate

- **Parent theory:** `(1)` and `(3)` are finite-dimensional rank bounds; `(4)` combines them with
  the finite Gibbs purity limit.  These components are classical.
- **Candidate residue:** the cofinal HT-faithfulness consequence and the joint invariant `(5)`,
  especially its product law `(7)`, require comparison with frame erasure, generalized
  condensation, and matroid-product literature.
- **Retirement condition:** downgrade to `[BRIDGE]` if the exact purity--constraint-capacity and
  multiplicative visibility law already appears in an equivalent parent formulation.

## Gates

- [x] finite rank bound and injective-capacity proof
- [x] purity consequence reduced to the exposed-face purity theorem
- [x] cofinal unbounded-degeneracy consequence proved on paper
- [ ] finite rank definitions and capacity bounds formalized
- [ ] nondegenerate Gram-to-capacity capstone formalized
- [ ] tensor rank and visibility product formalized
- [ ] parent-theory and literature audit completed
- [ ] pure-mathematical paper integration after novelty verdict
