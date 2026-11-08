# Natural cycle coordinates and exact boundary height

- **ID:** esg-cycle-height-structure
- **Stage:** 3-formalized
- **Type:** INTEGRAL CHAIN STRUCTURE

## Exact statements

Let `C_k(N)` be the actual exterior chains on prime labels with product at most
`N`, over any commutative ring. The boundary has vertex coefficient one.
Put `Z_k(N)=C_k(N)∩ker(d)` for positive exterior degree and `Z_0(N)=C_0(N)`.

1. `C_k(N)` is exactly the coordinate submodule on increasing prime supports
   of cardinality `k` and product at most `N`.
2. In positive exterior degree, `P=d(2∧·)` retracts `C_k(N)` onto `Z_k(N)`
   without changing height. These retractions commute with height inclusions.
3. Forgetting faces containing two gives a natural linear equivalence between
   `Z_k(N)` and the coordinate submodule on bounded odd prime supports.
   Its inverse sends `S` to `d(2∧S)=S−2∧dS`. These vectors form an actual
   basis of the cycle submodule.
4. The exact boundary image is `d C_(k+1)(N)=Z_k(⌊N/2⌋)`, including degree zero.
   For any weighted vertex functional, the forward containment in the half
   cutoff still holds.

These are submodules and maps of the existing prime-product exterior chains.
No rank assignment, hypothetical complex, or analytic premise is used.

## Paper proof

Sorting an injective prime tuple preserves its product and changes only the
exterior sign; repeated vertices give zero. This identifies the cutoff with
the corresponding exterior-basis span.

On any allowed face, `2∧d` replaces a deleted prime by two. The product cannot
increase. Cartan's identity `d(2∧·)+(2∧·)d=1` therefore makes `P` a retraction
to cycles at the same cutoff. Let `O` be exterior projection that forgets the
two-coordinate. The identities `cone O=cone` and `O cone=0` imply `PO=P` and
`OP=O`. Thus `O` and `P` restrict to inverse maps between cycles and odd chains.
Their formulas are independent of `N`, giving naturality.

Each boundary face has at most half the original product. Hence boundaries
at `N` are cycles below `⌊N/2⌋`. Conversely, adjoining two fills every cycle
at that smaller cutoff, within `2⌊N/2⌋≤N`. The augmented cone identity gives
the same conclusion for the empty face.

## Lean realization

Namespace `GaloisForLFunctions.EffectiveScalingGeometry`.

- [PrimeChainBasis.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeChainBasis.lean):
  `primeChainCutoff_eq_span_basis`, `primeChainCutoff_iff_repr_support`.
- [PrimeCycleProjection.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeCycleProjection.lean):
  `primeCutoffCycleRetraction_inclusion`, `primeCutoffCycleRetraction_natural`.
- [OddPrimeChainProjection.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/OddPrimeChainProjection.lean):
  `primeCycleProjector_comp_oddProjection`, `oddChainProjection_comp_cycleProjector`.
- [PrimeCycleCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeCycleCoordinates.lean):
  `primeCutoffCycleOddEquiv`, `primeOddCutoff_eq_span_basis`, `primeCycleToOdd_natural`.
- [PrimeBoundaryHeight.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeBoundaryHeight.lean):
  `primeChainBoundary_image_eq_half_cycles`, `primeChainBoundary_zero_image_eq_half`.

- [PrimeCycleBasis.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeCycleBasis.lean):
  `oddPrimeCutoffBasis`, `primeCutoffCycleBasis`, `primeCutoffCycleBasis_val`,
  `primeOddCutoff_zero`.

All six pass direct `lake --old env lean <module>` audits. Printed capstones
have exactly `[propext, Classical.choice, Quot.sound]`. All are imported by the
programme umbrella; no umbrella build is used.

## Contribution and remaining boundary

The corpus supplied doubled-cutoff fillings. This identifies the exact boundary
submodule and gives natural cycle coordinates at each height. The Betti-rank
formula is classical; see [Björner, Theorem 3.1](https://arxiv.org/abs/1101.5704).

The [actual homology comparison](esg-prime-homology-coordinates.md) now identifies
every augmented homology degree and its maps with surviving coordinates.
The natural integral barcode and canonical coefficient compatibility are proved in
[the integral persistence card](esg-integral-prime-persistence.md).
No Euler-cancellation estimate or scaling-surface effectivity is claimed.
