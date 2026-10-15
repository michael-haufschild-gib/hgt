# CHMD Stage 22 wiring and olean — 2026-10-15

User requested wiring and building `CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion`.

- Imported `GaloisForLFunctions.RHTower.CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion` in `formal/GaloisForLFunctions/RHTower.lean` (line 27163 at audit).
- Fixed four existing elaboration errors in Stage22: eta-expanded `chmdPoleWave` before `simp_rw` in continuity; replaced `gcongr` with explicit multiplication monotonicity/positivity for the archimedean bound; qualified `CHMDGrowthCollapse.kgWeight` in the two square-identity `unfold` tactics. Theorem statements unchanged.
- `lake --old build GaloisForLFunctions.RHTower.CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion` passed. Artifact: `formal/.lake/build/lib/lean/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.olean` (895352 bytes when built).
- Required final audit `lake env lean GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean` passed, exit 0, no diagnostics.
- Scoped `git diff --check` passed. No forbidden declaration or heartbeat override found in target source.
- Latest global `scripts/formal_tools.py lint` snapshot failed only for two unrelated modules unreachable from RHTower umbrella: `DeningerMeyerGlobalCausalSplitting`, `DeningerMeyerInvisiblePolynomialInjectivity`. Shared workspace was changing concurrently; Stage22 reachability is resolved. Do not infer global lint status from this historical snapshot.
- No full/umbrella build, commit or push. Temporary logs removed after verification.
