# Birelative fracture exactness and the abelian three-channel interaction obstruction

- **ID:** `birelative-fracture-square-and-three-channel-interaction`
- **Stage:** 3-formalized
- **Type:** FORMAL ALGEBRAIC BRIDGE / COMMON-LIFT EXACTNESS / POSITIVE NO-GO
- **Scientific status:** `[UNCONDITIONALLY LEAN-FORMALIZED] [PARENT MATHEMATICS]`
  `[ARCHITECTURAL CONSEQUENCE FOR HT] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/FacetRestrictionEmbedding.lean`
- **Statement:** Two quotient observations glue exactly when their difference vanishes modulo the
  sum of their gauge submodules.  For three abelian quotient channels, all pairwise defects can
  vanish while a precisely identified interaction quotient obstructs a common representative.

## Two-channel theorem

For submodules `I,J <= M`, Lean defines the common-lift and compatibility maps

```text
M/(I intersection J) -> M/I x M/J,
M/I x M/J -> M/(I+J),
(x,y) |-> x-y.                                               (1)
```

It proves:

```text
common-lift map is injective;
range(common-lift map)=kernel(compatibility map);
compatibility map is surjective.                             (2)
```

Consequently two observed quotient classes have a common representative exactly when their
compatibility defect vanishes, and any two common representatives differ by `I intersection J`.

## Strong three-channel no-go and positive receiver

For three submodules `I,J,K`, if every pairwise sum is `top`, every triple of observations is
pairwise compatible.  Nevertheless, if

```text
v notin (I intersection J)+K,
```

then `(0 mod I,0 mod J,v mod K)` has no common representative.

The theorem is not left negative.  Lean proves the exact positive classification

```text
(0 mod I,0 mod J,v mod K) has a common representative
  iff v in (I intersection J)+K.                             (3)
```

Thus `M/((I intersection J)+K)` is the residual interaction receiver for this family.  Higher
descent failure occurs already in abelian linear algebra; nonabelian associators are not required.

## Formal declarations

- `birelativeCompatibilityMap`
- `birelativeCommonLiftMap`
- `birelativeCompatibilityMap_mk`
- `birelativeCommonLiftMap_mk`
- `birelativeCommonLiftMap_injective`
- `range_birelativeCommonLiftMap_eq_ker`
- `birelativeCompatibilityMap_surjective`
- `exists_commonRepresentative_iff_compatible`
- `commonRepresentative_sub_mem_inf`
- `triplePairwiseCompatible`
- `triplePairwiseCompatible_of_pairwise_sup_eq_top`
- `pairwiseCompatible_without_commonTripleRepresentative`
- `zero_zero_third_has_commonRepresentative_iff`

## Novelty and anti-theatre gate

The module sequence, common-representative criterion, and failure of naive multi-ideal Chinese
remainder gluing are parent algebra.  They are not claimed as new scientific knowledge.

The nontrivial consequence for the HT program is architectural: a source-effectivity theory needs
independent realization directions and higher interaction groups even before nonlinear gauge
theory begins.  The result falsifies the narrower conjecture that higher HT obstruction layers
must arise only from noncommutative associators.

The bridge earns its place because it supplies both:

1. an exact positive two-channel gluing theorem; and
2. an exact positive quotient measuring a three-channel no-go.

It would be theatre to promote `(1)`--`(3)` as a new paper without constructing a natural HT
source whose independently defined realizations produce these submodules.

## RH boundary

The theorem explains a possible form of report-wide failure: several obstruction chains may be
pairwise compatible while not descending from one source-effective object.  It supplies no zeta
source cube, no positivity theorem, no critical-zero identification, and no RH implication.

## Verification

- Scratch elaboration passed before the declarations were inserted.
- The touched module is verified directly with its cached imports.
- No full build is required because the module already has a cached object file.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration is introduced.

