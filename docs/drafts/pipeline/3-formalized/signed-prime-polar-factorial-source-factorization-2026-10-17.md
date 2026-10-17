# Actual balanced sources for a grid-preserving factorial producer

- **ID:** signed-prime-polar-factorial-source-factorization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Signed prime–polar transport; explicit actual-source producer.
- **Count:** Contribution 10, one package including construction, arithmetic, and energy.
- **Paper:** `docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialSourceFactorization.md`
- **Endpoint:** `SignedPrimePolar.factorialSourceProducer_certificate` in
  `formal/GaloisForLFunctions/BiScaleUncertainty/SignedPrimePolarSourceCertificate.lean`.

## Proven result

For N=n+1 the actual C_c sources P_N,M_N have equal origin energies in
[6sqrt(N),46sqrt(N)]. Their signed autocorrelation contrast J_N=(h_P−h_M)/2
preserves W_N(log m) for every positive integer m and satisfies

|ν(J_N)|≤[10log(4N+1)+3+1/(4N)]/sqrt(N),  2≤∫J_N²≤32.

The exact pairing is [2B_N−a_N C_N]/sqrt(N), with
B_N=T(4N)−4T(2N)+4T(N), C_N∈[0,1], and
a_N=[(1+exp(log(1+1/(4N))/3))/2]³∈[1,1+1/(4N)].
The actual atom sequence is finite and absolutely summable; the polar integral
is admitted. The main theorem has only n:ℕ as input.

Construct a small-collar factorial ramp R_N and exponential tent density ρ_N,
then F_N(u)=R_N(−u), G_N(u)=exp(u/2)ρ_N(u). Integer separation preserves the
grid throughout the collar; finite Fubini evaluates both polar branches.
Reciprocal scaling P_N=N^(1/4)F_N+G_N/N^(1/4), M_N=N^(1/4)F_N−G_N/N^(1/4)
preserves the mixed correlation and improves the unbalanced O(N) origin-energy
cost to O(sqrt(N)). Their disjoint source supports give equal origin energies.

Arithmetic cancellation acts directly on T(N). No pre-floor counterterm,
Chebyshev discrepancy hypothesis, grid blindness, or positivity conclusion is used.
This constructs an actual source contrast; it leaves arbitrary signed packet
control and quantitative jump energy open. Contribution 11 subsequently closes
the jump-energy question for this family.

## Verification

- [x] Inspected source-factorization and factorial-producer precedents.
- [x] Dependency-closed paper proof, including reciprocal source balancing.
- [x] Actual C_c sources and numeric-index-only endpoint in Lean.
- [x] Thirteen final direct `lake --old env lean <leaf> -o <olean>` checks; empty logs.
- [x] Fifteen `/tmp` axiom audits; only propext, Classical.choice, Quot.sound.
- [x] All thirteen imports wired once; index refresh passes and lists the endpoint.
- [x] Formal lint run: nine unrelated unwired modules, no package-local error.

The facts ledger lists all leaves and unrelated lint errors. Evidence:
`/tmp/spp10-*-final.log`, `/tmp/spp10_final_axioms.lean`,
`/tmp/spp10-final-axioms.log`, `/tmp/spp10-index.log`, `/tmp/spp10-lint.log`.
No full/umbrella build, numerical experiment, commit, or push. README remained read-only.

## Prior-work and contribution boundary

The tent moment reuses `HTGeometry.integral_tiltedTentFullProfile`; the classical
moment, reciprocal scaling, and polarization are ingredients, not extra counts.
The complete new package joins literal compact sources, exact prime-grid values,
unconditional signed pairing, nonvanishing contrast size and quantified source cost.

Searches `/tmp/spp10-convolution-search.json` and `/tmp/spp10-tent-search.json`
are partial (reranking deadline and semantic timeout). Available candidates and
source arguments were inspected; no external novelty claim follows from retrieval.

Subsequent completed jump-energy package:
`3-formalized/signed-prime-polar-factorial-archimedean-cost-2026-10-17.md`.
