# Source-selected Gamma Ward shared-ghost classification (2026-08-16)

Formalized `formal/GaloisForLFunctions/RHTower/SourceSelectedGammaWardSharedGhostDescent.lean`, wired into `RHTower.lean`.

Heavy-conjecture results:
1. Fixed Cartier descent from resolved BV-Wold flatness fails: already RH-equivalent.
2. BRST reader killing Big-Witt diagonal while retaining offdiagonal fails: coherent fibre transports exact opposite full coefficients; cyclic correction retains physical residue.
3. Positive survivor: inverse-oriented prime-local ghost Ward equation has unique solution `c_p=p^(-t)`, so local ghost existence is fitted/vacuous.
4. One positive ghost independent of prime label satisfying equations at p=2 and p=3 exists iff t=0.
5. For Xi divisor t=2 Re rho-1, shared-ghost descent iff critical line iff existing `FrankensteinPrimeClockParacyclicSelectedWardDescendsAt` iff literal (2,3) Big-Witt seam zero; global statement iff RH.

Main declarations:
- `primeGammaInverseOrientedGhostWardEquation_iff`
- `primeGammaLocalInverseOrientedGhost_ward`
- `primeGammaLocalInverseOrientedGhost_unique`
- `primeGammaTwoThreeSharedInverseOrientedGhostWard_iff`
- `frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff_primeClockWard`
- `everyFrankensteinSourceSelectedGammaWardSharedGhostDescends_iff_riemannHypothesis`

Verification: direct lake env lean passed; exact leaf build passed; formal lint passed; axioms only propext, Classical.choice, Quot.sound. No umbrella build. No stale Lean process.

Open core sharpened: must derive prime-independent shared-ghost existence from genuine source/Gamma naturality. Prime-local countercharacters, common same-orientation corrections, and contractible fitted ghosts are insufficient. Frontier map updated.