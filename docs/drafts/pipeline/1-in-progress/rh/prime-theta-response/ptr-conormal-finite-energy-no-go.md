# PTR conormal finite-energy no-go

- **ID:** PTR-CONORMAL-L2
- **Stage:** 3-formalized (direct source check; targeted OLean audit pending)
- **Type:** route-class no-go and sharp regularity survivor
- **Proof chain attacked:** literal temporal-Maxwell infinite OAM/sideband boundary map → exact prime conormal ladder → independent defect confinement → RH.

## Source-grounded claim

`PhotonicPrimeCyclicSlabParabolicRealization` defines the exact target ladder as the bilateral eigenfamily `e ↦ λ^{-e}` for nonzero prime half-density multiplier `λ`. The corpus proves it is bilateral-moderate exactly at `Re s=1/2`, but has no finite-energy classification. The new claim is unconditional: `∑_{e∈ℤ}|λ^{-e}|²` is never finite, for any `s`; consequently no finite-energy `ℓ²(ℤ)` Maxwell boundary map can have this exact ladder as its output, even on the critical line.

## Proof and survivor

If both tails were square-summable, their terms would tend to zero. At symmetric grades `n,-n`, however, the ladder values multiply to `1`, so the products of their squared norms are identically `1`, a contradiction. The sharp positive regularity survivor is the already-proved source theorem `bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half`: the target is tempered/moderate exactly on the critical wall, but never finite energy. Thus the remaining PTR boundary map must be distribution-valued or use a singular/rigged boundary trace; simply enlarging a finite port to a bounded finite-energy sideband Hilbert map cannot realize the target. This does not kill all PTR or supply independent defect confinement.

## Audit

- Corpus search: `bilateralEigenFamily`, `photonicPrimePCMConormalSideband_eq_bilateralEigenFamily`, `bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half`; no matching square-summability no-go returned. Deep search found one-sided geometric-tail and weighted lattice summability methods.
- Novelty is source-specific, not a claim that the elementary bilateral-geometric lemma is new to mathematics. Broad arXiv checks found no exact prime-conormal/Maxwell finite-energy statement; exhaustive literature novelty is unverified.
- Abstract proof passed `lake env lean /tmp/ptr_l2_scratch.lean`. The physical no-go and moderate-but-not-finite-energy iff passed `lake env lean GaloisForLFunctions/RHTower/PhotonicConormalFiniteEnergyNoGo.lean` with one foreground process; module is wired in `RHTower.lean`. Targeted `lake build GaloisForLFunctions.RHTower.PhotonicConormalFiniteEnergyNoGo` replayed 8,800+ dependencies and was interrupted before OLean emission to respect bounded-build discipline. Global lint failed only on concurrently edited, unrelated `HTGeometry/PolynomialODEEvenCompactGap*` files (unreachable modules and raised heartbeat budgets). No umbrella build.
