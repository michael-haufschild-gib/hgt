# Sharp tripled-height contraction for prime weights

- **ID:** esg-prime-weighted-contraction
- **Stage:** 3-formalized
- **Type:** WEIGHTED CHAIN HOMOTOPY

## Exact theorem

Give each prime vertex boundary coefficient equal to that prime, over any
commutative ring. The difference of the prime-three and prime-two cones
contracts the actual augmented complex and increases prime-product height
by at most three. It commutes with height inclusions.

The actual inclusion from height `N` to `3N` is nullhomotopic. Consequently
every actual augmented homology persistence map from `N` to `3N` is zero.
Over the integers, the empty generator at height one cannot be filled at
height two. Three is therefore the least uniform integer dilation for
augmented fillings.

## Proof

For a prime `p`, Cartan's identity is `d(p∧·)+(p∧·)d=p·id`.
Subtracting the identities for three and two gives `dh+hd=id` for
`h=3∧·−2∧·`. Both summands lie below `3N`. The maps are restrictions of
one ambient linear map, so they commute with every height inclusion.
The restricted Cartan identities are exactly the chain-homotopy equations,
including degree zero. Homotopic maps induce the same homology map.

At height two, every allowed vertex is prime two. Its weighted boundary
has even empty-chain coefficient. Reduction of that coefficient modulo two
kills every boundary, while the height-one empty generator maps to one.
Hence this generator has no filling at height two.

## Lean realization

[PrimeWeightedContraction.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedContraction.lean),
namespace `GaloisForLFunctions.EffectiveScalingGeometry`:

- `primeBezoutCone_contracts`, `primeBezoutCone_contracts_zero`.
- `primeValueCycle_fills_triple`, `primeValueZero_fills_triple`.
- `primeBezoutCutoffCone_natural`.
- `primeValueInclusionNullhomotopy`, `primeValueHomology_triple_zero`.
- `primeValueEmpty_not_filled_at_two`.

Direct `lake --old env lean` audit passes. Printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`. Imported by the programme umbrella.

## Scope

Cartan contraction and weighted simplicial homology are classical. The result
supplies the sharp integer dilation and actual persistence nullhomotopy for
prime-product cutoffs. It does not identify all weighted torsion or establish
Euler cancellation. Torsion classification remains on the
[separate card](../1-in-progress/esg-prime-weighted-torsion-classification.md).
