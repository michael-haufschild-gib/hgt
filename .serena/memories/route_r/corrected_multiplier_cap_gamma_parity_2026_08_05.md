# Route R corrected multiplier cap and Gamma parity

Formalized source frontier in `RHTower/RouteRPreDivisorRationalAdelicMultiplierKOneHomology.lean`, `RHTower/RouteRPreDivisorRationalAdelicCorrectedMultiplierXiLanding.lean`, and `RHTower/RouteRCorrectedMultiplierGammaOrientationDescent.lean`.

Key results:
- Unitized actual Bruhat core multiplier crossed product has genuine prime K1 `HH1` class detected by Kummer regulator `log p`.
- Raw Bruhat-decorated atom is repaired by canonical potential `b_p=(p^-1•a)*a-1`; corrected cycle has zero Hochschild boundary, regulator `-log p`, and exact nonzero Xi landing equal to signed Kummer landing.
- Cap corrected multiplier class into retained rational-adelic relative H1 using explicit Hodge coefficient K. Period-one Stokes regulator reads `K * landing`, so cap null iff K=0.
- Fixed same-source Gamma parity is equivalent to K=0/source-dagger/same-fibre norm/RH.
- Hostile test: genuine cyclic source dagger flips corrected Kummer period from `-log p` to `+log p`; rotated HH1 class is distinct. Dagger-transported Gamma naturality then holds unconditionally because source and Hodge signs cancel. Thus functional-equation reflection cannot supply annihilation. Remaining producer must be independent same-fibre fixed-orientation singular law.

Card: `docs/drafts/pipeline/1-in-progress/route-r-kummer-cyclic-one-cocycle-detector.md`, KCC-1..6 proved, KCC-7 falsified, KCC-8 open.

Audit: targeted `lake build GaloisForLFunctions.RHTower.RouteRCorrectedMultiplierGammaOrientationDescent` passed. Axioms only `[propext, Classical.choice, Quot.sound]`. Global lint currently fails only on concurrent unrelated unreachable HTGeometry modules `PhysicalRealizationCarrierTransport` and `SiteFactorGraphWitness`.