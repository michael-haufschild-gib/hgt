# HB source-real swap-equivariant response blindness

- **ID:** C-HB-SWAP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Time-dependent nonlinear response on any swap-invariant partial domain remains swap-related; every invariant reporter is blind, while nonzero-charge actual theta states are not occupation-aligned.

## Goal

Killed HB producer class:

`source reality + swap-equivariant response` → no-charge-sector selection → aligned double KMS → zero Hawking charge → RH.

## Result

- Exact actual visible/partner charged theta states; no fitted vectors.
- No linearity, continuity, differentiability, boundedness, total-domain, finite-energy, Fock, or Schatten assumption.
- Positive survivor: physical domain, evolution, or reporter must carry oriented/chiral swap breaking.
- Literature audit: charged TFD factorization and TFD dynamical symmetry are known; exact theta-source partial-history route kill was not found.

## Lean

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingHBSourceRealSwapEquivariantPartialResponseNoGo`
- Certificate: `d4HBSourceRealSwapEquivariantNeutralSectorRouteKilled`
- Direct Lean: PASS
- Target build: PASS (`11000` jobs)
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Lint: new module reachable; repository lint fails only on pre-existing unreachable modules.

## Novelty

`[NEW ROUTE-SPECIFIC CONSEQUENCE]`: general equivariant-orbit blindness is structural; its application to actual theta charged states, arbitrary invariant partial domains, non-autonomous nonlinear dynamics, and HB neutral-sector localization was absent from corpus and located literature.
