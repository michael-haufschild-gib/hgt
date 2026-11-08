# Canonical integral coefficient extension of prime homology

- **ID:** esg-integral-chain-coefficients
- **Stage:** 3-formalized
- **Type:** CHAIN-LEVEL COEFFICIENT EXTENSION

## Exact statement

For every commutative ring `R`, the canonical map from integral prime vertices
to the same vertices over `R` extends to the actual exterior-chain modules.
It sends each ordered prime wedge, and each increasing exterior basis face,
to the same wedge or face. It commutes with the unweighted boundary, adjoining
any prime, and every height inclusion. It preserves every prime-product cutoff.

Surviving odd faces form a basis of actual augmented homology. Base-changing
the integral basis gives a linear equivalence
`R ⊗[ℤ] H_k(C(N);ℤ) ≃ H_k(C(N);R)`. On `r⊗x`, each surviving coordinate is the
corresponding integer coefficient of `x` multiplied by `r`.
This equivalence is the canonical extension of the actual homology map:
`r⊗x ↦ r·H(ℤ→R)(x)`. It commutes with every height-persistence map.
No flatness assumption on `R` is needed.

## Proof

The coefficient-ring wedge is alternating over the integers. Compose it with
the free integral prime-vertex map and descend through the exterior universal
property. Its value on a prime wedge is the same coefficient-ring wedge.

The actual boundary is the signed sum of prime deletions, with integer
coefficients. Linearity therefore gives boundary compatibility. Adjoining a
prime has the same wedge formula. Cutoff generators retain their exact prime
products, and the map is independent of the height, proving cutoff preservation
and naturality of its restrictions.

The established actual-homology coordinate isomorphism supplies its basis.
The base-changed integral basis has vectors `1⊗b_s`; send these to the same
coefficient-ring homology basis. The tensor-basis coefficient formula gives
the stated expression on every pure tensor.

The canonical chain map sends cycles to cycles and boundaries to boundaries,
so it descends through the actual boundary quotient. Its class formula is
`[c] ↦ [c_R]`; literal chain inclusions prove height naturality. Transport
through the adjacent-complex comparison gives the original homology map.

For a surviving odd face `S`, the basis class is represented by `d(2∧S)`;
in degree zero it is represented by the empty chain. Chain extension preserves
these representatives. The induced homology map therefore preserves every
basis vector. Equality on the base-changed basis proves canonical agreement;
linearity gives the pure-tensor formula and height naturality.

## Lean realization

[PrimeIntegralCoefficients.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeIntegralCoefficients.lean),
namespace `GaloisForLFunctions.EffectiveScalingGeometry`:

- `primeIntegralChainMap_atom`, `primeIntegralChainMap_basis`.
- `primeIntegralChainMap_boundary`, `primeIntegralChainMap_cone`.
- `primeIntegralChainMap_cutoff`, `primeIntegralCutoffMap`.
- `primeIntegralCutoffMap_boundary`, `primeIntegralCutoffMap_natural`.

[PrimeHomologyTensorCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeHomologyTensorCoordinates.lean):
`primeHomologyCriticalBasis`, `primeHomologyCoordinateBaseChange`,
`primeHomologyCoordinateBaseChange_basis`, `primeHomologyCoordinateBaseChange_tmul`.

[PrimeHomologyCoefficientMap.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeHomologyCoefficientMap.lean):
`primeIntegralHomologyMap_class`, `primeIntegralHomologyMap_natural`.

[PrimeHomologyBaseChange.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeHomologyBaseChange.lean):
`primeIntegralHomologyMap_basis`, `primeHomologyBaseChange_one_tmul`,
`primeHomologyBaseChange_tmul`, `primeHomologyBaseChange_natural`.

All four direct `lake --old env lean` audits pass. Printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`. Imported by the programme umbrella.

The explicit odd-squarefree coordinate version belongs to the
[integral persistence theorem](esg-integral-prime-persistence.md).
