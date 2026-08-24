# Operator-theory Stage 2 formalization (2026-08-24)

## Completed cards
- Promoted `infinitesimal-hardy-leakage-horizontal-layer-resolvent` to Stage 3.
- Promoted `wold-boolean-diagonal-renormalization-mismatch` to Stage 3.

## Wold incomplete tensor product
- `HTGeometry.IncompleteTensorProduct` is the canonical implementation: von Neumann incomplete ITP as `KernelHilbert` completion of finite-excitation elementary pure tensors with exact product Gram kernel. Do not duplicate it with a pointed-basis ℓ² coordinate model.
- `RHTower.WoldThermofieldIncompleteTensorProduct` specializes to local `ℓ²(ℕ₀×ℕ₀)` thermofield factors and critical Wold reference vectors.
- Added exact missing sector criterion `exists_tendsto_primeWoldTwistedFinitePacket_iff`: cofinal twisted finite packets converge strongly in the critical ITP iff `c = 0`.
- Noncritical proof: for `N ≤ M`, packet overlap is exact Hellinger tail ratio `H_M/H_N`; fixed-head overlaps tend to zero. Any putative strong limit is unit by norm continuity, but orthogonal to every packet and hence to itself, contradiction.
- Moved `mem_primesBelowSubtype_iff`, `monotone_primesBelowSubtype`, and `cofinal_primesBelowSubtype` down to `PrimeWoldGammaGlobalBoundaryVolume`, preserving names in namespace `RHTower`; removed duplicate declarations from `MobiusPlueckerNormalConeDiagonalLift`.

## Verification
- Direct Lean checks passed for `PrimeWoldGammaGlobalBoundaryVolume.lean`, `MobiusPlueckerNormalConeDiagonalLift.lean`, and `WoldThermofieldIncompleteTensorProduct.lean`.
- Targeted leaf build passed for `GaloisForLFunctions.RHTower.WoldThermofieldIncompleteTensorProduct`; no umbrella build run.
- New theorem axiom reports: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint has only concurrent unrelated unreachable modules: `RHTower.AnalyticHermitianClosedSpanRealization`, `RHTower.ThetaCuspHawkingEKGCausalMirrorOpticalLaw`, `HTGeometry.InfiniteBlaschkeMultiplier`.

## Remaining Stage 2 cards in this route
- `window-riesz-gap-target-equivalence`
- `de-branges-ht-gauge-saturation`
- `euler-hardy-leakage-offline-zero-rank` and other untouched cards under `07-functional-analysis-operator-theory`.
