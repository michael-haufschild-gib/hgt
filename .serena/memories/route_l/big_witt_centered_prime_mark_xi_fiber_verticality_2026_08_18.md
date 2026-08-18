# Big-Witt centered-prime-mark / completed-Xi fiber frontier (2026-08-18)

- Formal module: `formal/GaloisForLFunctions/RHTower/DeningerBigWittCenteredPrimeMarkXiFiberComparison.lean`.
- Capstone: `deningerBigWitt_centeredPrimeMark_completedXiSpectralFiberComparison`.
- Exact survivor: F₂ advances the Teichmüller centered-mark orbit; orbit level k equals arithmetic base change p ↦ p^(2^k) at fixed completed-Xi spectral label and also equals the scalar reporter at dilated label 2^k α.
- Critical distinction: arithmetic-base equality is source-induced; horizontal relabeling does not construct transport between completed-Xi theta fibers. Any total α ↦ 2α fiber transport would require XiC α = 0 → XiC (2α) = 0, the missing divisor-stability input.
- Strong no-go: on every right-half completed-Xi theta fiber, the base-2 Frobenius reporter orbit is injective, so finite preperiodicity/collision cannot be the source mechanism.
- Audit: direct `lake env lean` and targeted module `lake build` pass; `#print axioms` shows only propext, Classical.choice, Quot.sound. Module wired into `GaloisForLFunctions.RHTower` without umbrella build.
- Paper/formal card: `docs/drafts/pipeline/3-formalized/big-witt-centered-prime-mark-completed-xi-spectral-fiber.md`.