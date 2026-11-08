# Actual prime-weighted homology over every coefficient ring

- **ID:** esg-all-coefficient-weighted-homology
- **Stage:** 3-formalized
- **Type:** ARITHMETIC PERSISTENCE CLASSIFICATION
- **Status:** Actual core decomposition, height maps, integer coefficient extension and binary intervals formalized

## Theorem

For every commutative ring `R`, actual augmented prime-weighted homology
splits naturally into cores indexed by squarefree integers `m` coprime to six.
Writing `k=ω(m)`, the core contributes exactly:

| Degree | First window | Second window | Crossing map |
|---|---|---|---|
| `k` | `R[m,2m)` | `R/2R[2m,3m)` | Reduction modulo two |
| `k+1` | `Ann_R(2)[2m,3m)` | `R[3m,6m)` | Inclusion into `R` |

Each branch is zero outside its displayed windows. Within a window its
coefficient persists unchanged. The comparison uses original cycle classes,
preserves every height inclusion and identifies canonical integer coefficient
extension with the scalar map on both quotients.

Over `𝔽₂`, each core gives the two intervals `[m,3m)` and `[2m,6m)` in
consecutive degrees, including the empty core `m=1`.

## Proof

The [two-prime normal form](esg-two-prime-weighted-normal-form.md) gives an
integral, height-preserving change of actual exterior basis. A core omits two
and three; its four tags have births `m,2m,3m,6m`, with differential row
`(2,3)` and column `(-3,2)`.

Before `2m`, only the bottom generator occurs. On `[2m,3m)`, multiplication
by two gives bottom `R/2R` and middle `Ann_R(2)`. On `[3m,6m)`, the row is
surjective because `3−2=1`. Its kernel is uniquely `(3c,−2c)`, with coefficient
`c=a+b`. At `6m`, the top column fills this kernel injectively. Middle inclusion
retains an annihilator coefficient because `(a,0)=(3a,−2a)` when `2a=0`.
Bottom inclusion gives reduction modulo two.

Project the transformed basis onto each core. These cutoff-preserving
orthogonal idempotents commute with the boundary and sum to the identity on
each chain's finite support. Their induced homology ranges give the canonical
sum `Hₖ(C(N);R) ≃ ⨁c range(Pₖ,c)`. Tagged realization and coordinate extraction
are inverse on each range. They identify bottom and middle homology with the
calculated scalar quotients; unsupported degrees vanish, and top cycles vanish
by injectivity of `(-3,2)`. These comparisons preserve the actual height maps.

The transformed basis is defined over the integers, so every coordinate of
an extended chain is the canonical scalar image of its integer coordinate.
This map preserves cycles, boundaries, core projections and each quotient
relation. Passing actual cycle classes through extraction proves both
coefficient diagrams. In characteristic two, the lower relations vanish
before `3m`, while every upper scalar is a cycle from `2m`; hence the joined
binary intervals. Unique prime factorization identifies cores with squarefree
integers coprime to six and cardinality with `ω(m)`.

## Lean realization

All modules lie in `EffectiveScalingGeometry` and are wired into its umbrella.
The principal declarations are:

| Content | Declarations |
|---|---|
| Actual homology sum and height maps | `twoPrimeHomologyCoreEquiv`, `twoPrimeHomologyCoreEquiv_natural` |
| Original core quotients | `twoPrimeLowerCoreCoefficientEquiv`, `twoPrimeUpperCoreCoefficientEquiv` |
| Degree support | `twoPrimeCoreHomologyProjection_supported` |
| Quotient height compatibility | `twoPrimeLowerCoreCoefficientEquiv_natural`, `twoPrimeUpperCoreCoefficientEquiv_natural` |
| Crossing maps | `twoPrimeLower_free_modTwo_transition`, `twoPrimeUpper_annihilator_free_transition` |
| Original integer extension | `primeWeightedIntegralHomologyMap_class`, `primeWeightedIntegralHomologyMap_core`, `primeWeightedIntegralHomologyMap_natural` |
| Scalar coefficient diagrams | `twoPrimeLowerHomologyCoefficient_integral`, `twoPrimeUpperHomologyCoefficient_integral` |
| Binary intervals and maps | `twoPrimeBinaryLowerCoreEquiv_natural`, `twoPrimeBinaryUpperCoreEquiv_natural`, `twoPrimeBinaryLowerCore_outside`, `twoPrimeBinaryUpperCore_outside` |
| Arithmetic labels | `twoPrimeCoreArithmeticEquiv`, `twoPrimeCoreHeight_degree` |

Direct module audits pass; transitive axioms are contained in
`propext`, `Classical.choice`, `Quot.sound`.

## Gain and boundary

The [integral classification](esg-prime-weighted-torsion-classification.md)
already identifies free-to-parity persistence. The new classification retains
annihilator classes over arbitrary rings, their actual height transitions and
the canonical integer map. A tensor-homology base-change claim would lose the
new annihilator classes over rings with 2-torsion. This result supplies no
signed Euler cancellation or arithmetic height sign.
