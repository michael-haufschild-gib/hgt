# Distributive coordinate-facet effectivity

- **ID:** `distributive-coordinate-facet-effectivity`
- **Stage:** 3-formalized
- **Type:** FORMAL ALGEBRAIC BRIDGE / FINITE DESCENT / POSITIVE NO-GO SUCCESSOR
- **Scientific status:** `[UNCONDITIONALLY LEAN-FORMALIZED] [PARENT MATHEMATICS]`
  `[NOT AN RH RESULT]`
- **Successor:** `calibrated-fracture-incidence-kernel-cokernel.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/FacetRestrictionEmbedding.lean`
- **Statement:** Pairwise compatibility is not sufficient for arbitrary finite quotient channels,
  but it is sufficient for coordinate-facet ideals.  Every compatible finite facet packet has one
  global polynomial representative, unique modulo the Stanley--Reisner nonface ideal.

## General distributive-family theorem

For submodules `J_i<=M`, define

```text
IsFractureDistributive(J)
  iff J_i + intersection_(j in s) J_j
      = intersection_(j in s) (J_i+J_j)
```

for every `i` and every finite `s`.  Lean proves that under this law a finite packet
`x_i in M/J_i` has a common ambient representative exactly when every pairwise birelative defect
vanishes.  Any two common representatives differ by `intersection_(i in s) J_i`.

This is the exact positive boundary of the already formalized three-channel counterexample:

```text
[NO-GO] pairwise compatibility implies global effectivity for arbitrary quotient channels;
[POSITIVE] it does imply global effectivity on every finite distributive fracture family.
```

## Coordinate-facet specialization

For `F,G` finite variable sets, the coordinate ideals satisfy

```text
facetIdeal(F)+facetIdeal(G)=facetIdeal(F intersection G).
```

A coefficientwise monomial proof then establishes the complete finite distributivity law.  Hence a
packet

```text
x_F in R[X]/facetIdeal(F)
```

has a common polynomial representative iff all pairwise defects vanish.  If `P,Q` represent the
same packet, then

```text
P-Q in stanleyReisnerIdeal(facets).
```

The last conclusion uses the independently formalized identity expressing the Stanley--Reisner
ideal as the intersection of the coordinate-facet ideals.

## Formal declarations

- `familyPairwiseCompatibleOn`
- `IsFractureDistributive`
- `exists_commonFamilyRepresentative_of_pairwiseCompatible`
- `exists_commonFamilyRepresentative_iff`
- `commonFamilyRepresentative_sub_mem_inf`
- `facetIdeal_sup`
- `facetIdeal_isFractureDistributive`
- `exists_commonFacetPolynomialRepresentative_iff`
- `commonFacetPolynomialRepresentative_sub_mem_stanleyReisnerIdeal`

## Novelty and anti-theatre gate

Finite distributive Chinese-remainder gluing, monomial-ideal distributivity, and inverse-limit
descriptions of face rings are established parent mathematics.  These Lean declarations are not a
new scientific result and do not warrant a paper by themselves.

Their scientific use is exact: they prove that the natural Stanley--Reisner facet channels avoid
the higher interaction obstruction present for arbitrary submodules.  When combined with an
independently proved analytic identification of an HT structural module with a face ring, they
show that its unpolarized kinematic descent is effective.  Any remaining obstruction must live in
the analytic, pointed, polarized, bornological, integral, or derived coupling—not in H0 gluing.

## Verification

- The existing cached object file was present, so no build was run.
- The touched Lean file passed direct elaboration with `lake env lean`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration was introduced.
