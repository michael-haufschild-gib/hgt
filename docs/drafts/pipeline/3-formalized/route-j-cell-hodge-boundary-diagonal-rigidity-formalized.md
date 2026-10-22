# Route J cell Hodge-boundary diagonal rigidity — formalized closure

- **ID:** `route-j-cell-hodge-boundary-diagonal-rigidity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./route-j-cell-hodge-boundary-diagonal-rigidity.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NO RH INPUT]`

## Lean module

`GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity`
(namespace `RHTower.PrimitivePromotedCellHodgeRigidity`; umbrella `GaloisForLFunctions.RHTower`).

## Formal theorem chain

1. `canonicalCellDefectGenerator`, `canonicalCellPacketGenerator`, `cellDefectCoordinate`,
   `cellPacketCoordinate` with
   `cellDefectCoordinate_canonicalDefectGenerator`,
   `cellDefectCoordinate_canonicalPacketGenerator`,
   `cellPacketCoordinate_canonicalPacketGenerator`,
   `cellPacketCoordinate_canonicalDefectGenerator` — the cell defect/packet coordinate maps and
   their Kronecker values `(CHB-4)`, `(CHB-5)`.
2. `cellScalarExterior`, `cellScalarExterior_ιMulti`,
   `cellScalarExterior_canonicalDistinctCellCarrier` — linearization of `(CHB-1)` on the exterior
   square.
3. `cellReflectionOddBoundaryCoordinate`, `cellReflectionOddBoundaryDefect`,
   `cellReflectionOddBoundaryCoordinate_canonicalDistinctCellCarrier`,
   `cellReflectionOddBoundaryCoordinate_shiftedCarrier` — the exact Kronecker law `(CHB-2)`.
4. `xiGammaEulerBoundaryHalfHeight_cell_injective` — distinct prime/depth cells have distinct
   half-heights `(CHB-8)`.
5. `cellReflectionOddBoundaryDefect_carrierCombination_injective`,
   `canonicalDistinctCellCarrierCombination_injective`,
   `canonicalCarrierCombination_not_mem_actualCellGammaAdmittedHodgeSector` — the rigidity
   `(CHB-3)`/`(CHB-12)`: at nonzero modular displacement, the actual boundary defect is injective
   on the whole finite canonical distinct-cell carrier span.
6. `sourceNormalDepthSpreadCoefficients_ne_zero`,
   `sourceNormalDepthSpreadCarrier_not_mem_actualCellGammaAdmittedHodgeSector` — the finite
   depth-spread corollary `(CHB-11)`: neither the one-sided spread nor its doubled reflected
   version is admitted.
7. `shiftedCarrier_not_mem_actualCellGammaAdmittedHodgeSector` — the single-witness statement the
   rigidity theorem upgrades.

The predecessor-card correction is in place: `1-in-progress/route-j-primitive-promoted-euler-
exterior-source.md` now explicitly refuses to identify the compensated finite-index fixed sector
with `ker(actual Gamma/Hardy boundary reflection defect)` and cites the rigidity theorem.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity.lean`
  — clean, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity`
  — green.
- `#print axioms` on statements 3–7: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present in `GaloisForLFunctions/RHTower.lean`.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: novelty unverified; `[OPEN CORE]` corona relation remains open

The `[OPEN CORE]` named on the paper card — construct a source-derived corona relation with a
bounded first-clock comparison, or prove class-completely that every such relation loses the
first-clock readout — is a Route J research gate, not formalization debt for this theorem.
