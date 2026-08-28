# SC holomorphic prime-log zero condensation (2026-08-28)

Formalized hard-frontier structural obstruction in `formal/GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicPrimeLogZeroCondensation.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/sc-holomorphic-prime-log-zero-condensation.md`. Read-only frontier map was not edited by this work (it remained concurrently modified in worktree).

Corpus-origin conjecture loop:
1. Exact real SC neutral packet determinant is product of signed Gamma-Bocksteins.
2. Coefficient-faithful entire complexification `a_p(exp(-z log p)-exp(z log p))` has Bockstein zero lattice `pi*i*Z/log p`.
3. Strong full-clock transfer conjecture fails after allowed central-pole cancellation because the central lattice point can be removed.
4. Pivot: terminal packet prime supplies noncentral zero `z_m=pi*i/log(p_{m+1}) != 0` with `z_m -> 0`. Any scalar regularizer finite at `z_m` preserves this zero, so locally uniform convergence forces target value 0 at origin, contradicting normalized Xi value 1.

Main results:
- `preDivisorHolomorphicPrimeBockstein_ofReal`: exact real-axis Gamma-Bockstein identity.
- `preDivisorRiggedPrimeHolomorphicPacket_ofReal`: exact realification equals prior rigged SC neutral determinant.
- `preDivisorRiggedPrimeHolomorphicPacket_zeroCondensation`: positive structural survivor, noncentral packet zeros condense at wall origin.
- `not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicPacket_scalarFactor`: excludes arbitrary packet-growing central-pole-only scalar factorizations, with no regularity assumption on scalar beyond finite complex value at moving zeros.

RH burden delta: all SC scalar regularizations that cancel only the growing central wall zero are closed. Viable landing must have matching packet-dependent meromorphic poles at moving noncentral prime-log zeros (condensing at origin), or break primewise determinant factorization via genuine cross-prime/operator coupling.

Novelty: `[NOVELTY UNVERIFIED]`. Connes--Consani know `2pi*i Z/log p` local-factor lattice; application to signed SC Bockstein half-lattice and compact-open Xi landing no-go was not found. Britz et al. and Hartmann--Lesch confirm regularized Fredholm corrections are exponential/zero-free and preserve divisor.

Verification:
- source check PASS: `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicPrimeLogZeroCondensation.lean`
- exact leaf build PASS: `lake build GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicPrimeLogZeroCondensation`
- four scoped capstones have axioms exactly `[propext, Classical.choice, Quot.sound]`
- forbidden-declaration scan and scoped diff check clean
- global lint sees new module reachable, fails only unrelated concurrently unwired modules
- no umbrella/full build run.