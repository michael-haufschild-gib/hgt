# EWU: exact signed evenization and finite-pole source uniqueness

Status: formalized. All four oleans built; all four direct Lean audits passed. Evidence source: current Lean corpus only. No external search or novelty audit, per user instruction.

## Objective

Prove a structural theorem removing an actual obstacle in EWU, not another criterion or an improved estimate. Final claims must be unconditional, compiled, wired, and audited directly with `lake env lean`.

## Verified frontier

- `EvenSectorFullPositivity.weilPositiveEvenAt_one_iff` already identifies the cone at pole weight one.
- `EvenSectorPoleWeightWindow.one_le_of_primeBlindPositiveEvenAt` excludes pole weights below one.
- `EvenSectorDoublePoleExclusion.canonical_or_negative_superpole` eliminates the negative double-pole branch at arbitrary pole weight; a noncanonical source must have negative-part Dirichlet divergence at some exponent greater than one.
- `EvenSectorPoleFreeTwoSidedGrowth` supplies polynomial coefficient growth without an extra assumption.
- `EvenSectorPoleFreeResonatorPositivity` transfers positivity only to nonnegative-coefficient translated packets. Signed coefficients can change sign on the imaginary spectral segment.
- `EvenSectorTwistedArcNull` eliminates that segment at pole weight one using a genuinely null twisted-arc family. Extra pole weight leaves a nonzero budget in the same identity.

## Conjecture ledger

1. Extend the pole-weight-one spectral argument verbatim to arbitrary pole weight. Rejected: the null identity gains the pole budget; assuming it remains null is circular.
2. Multiply the twisted-arc family by the pole annihilator. Unresolved: spectral pole removal is exact, but multiplication differentiates the physical blind kernel; pointwise blindness at logarithmic nodes does not imply derivative blindness. Must not assume this closure.
3. Investigate the signed resonator obstruction and the exact geometry of the imaginary segment. Seek a structural operation that removes this obstruction using existing arithmetic constraints, rather than adding a convergence premise.

4. **Rationally shifted reflection eliminates every unwanted arithmetic node.** Survives preliminary attack. For `N >= 1`, put `M = 2*N^2+2`, `D = (M+1)*N^2`, `alpha = (M+1)/M`, `delta = log(alpha)/2`, and `w = 1/(D+1)`. Use the existing even polar-free bump `g_w`, supported in `[-w/4,w/4]`. For arbitrary real coefficients supported on `[1,N]`, set
   `F(x) = sum_m c_m [g_w(x-log(m)-delta)+g_w(x+log(m)+delta)]`.
   The test is even and pole-free. Reflected cross-correlations are centered at `+-log(alpha*m*k)`. They meet no `+-log(n)`, including `n=1`: equality would give `M*n=(M+1)*m*k`, impossible since `0<m*k<=N^2<M`. The corpus integer logarithmic gap applied to these cleared integer numerators gives separation at least `1/(D+1)`. The profile autocorrelation has radius `w/2`, so every reflected arithmetic interaction is exactly zero. Direct interactions still select precisely `m=n*k`.

## Dependency-closed paper proof for conjecture 4 and EWU closure

1. The preceding arithmetic argument gives `k_F(log n)=2*k_g(0)*sum_m c_(nm)*c_m` for all `n>=1`. Its negative-node value is the same. No coefficient sign is used. The same zero-node identity for the derivative profile gives the exact two Plancherel masses: `integral |Fhat|^2=4*pi*k0*sum c_m^2` and `integral |Fhat'profile|^2=4*pi*k1*sum c_m^2`.
2. Pole-free even positivity and the exact explicit formula bound the surviving signed multiplicative quadratic form by the archimedean energy. The existing bound `A(t)<=log(1+|t|)+4` gives `A(t)<=log(1/w)+9/2+w^2*t^2/2`. The existing profile identity gives `w^2*k1<=profileRatio*k0`. Therefore `2*sum_n lambda_n/sqrt(n)*sum_m c_(nm)c_m <= (log(D+1)+9/2+profileRatio/2)*sum c_m^2`.
3. Since `D+1=2*N^4+3*N^2+1<=6*N^4` for `N>=1`, its logarithm is at most `4*log N+log 6`. On each primitive set choose `c_1=1`, `c_n=t*lambda_n/sqrt(n)`. The exact surviving arithmetic form is `t*sum lambda_n^2/n`; all other multiplicative pairs vanish by primitivity. Optimizing this quadratic inequality gives the usual primitive mean-square law with `4*log N+C`. On dyadic blocks, the existing AM-GM argument gives `sum |lambda_n|=O(N log N)`. Geometric summation proves absolute Dirichlet convergence at every exponent greater than one.
4. For a source positive at any finite pole weight, apply the public `no_negative_double_pole_of_weilPositiveEvenAt` with the absolute convergence just proved, then the public `riemannHypothesis_of_weilPositiveEvenAt_of_abel`. Thus the source is exactly von Mangoldt on `n>=2`. This eliminates the remaining superpole branch rather than reformulating it as a receiver. The earlier private convergence-to-canonical helper need not be accessed.

Attack checks: the rational shift depends on `N`, but its required inverse width is polynomial, so the archimedean cost stays logarithmic. Every reflected node is excluded, not sampled. The profile is already polar-free, so changing its position introduces no pole slack. The source coefficients need no assumed sign or growth. Search found no existing version of this arithmetic reflection cancellation; search compiler metadata was largely source-only, so all dependencies will be checked by Lean.

## Formalization progress

- Arithmetic separation: `EvenSectorDetunedReflection.lean`, targeted olean build passed.
- Exact signed packet identities: `EvenSectorDetunedPackets.lean`, targeted olean build passed.
- Archimedean integration: `EvenSectorDetunedToeplitz.lean`, targeted olean build passed.
- Unconditional construction and source uniqueness: `EvenSectorPoleWeightUniqueness.lean`, targeted olean build and direct `lake env lean` audit passed.
- All four modules wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- `/tmp` axiom/API audit passed. The exact packet identity, signed form, unconditional realization, and source-uniqueness theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py index` completed. Repository lint reported seven unrelated modules unreachable from the RHTower umbrella; no error concerns these four modules.
- Final direct `lake env lean` audits passed without diagnostics for `EvenSectorDetunedReflection.lean`, `EvenSectorDetunedPackets.lean`, `EvenSectorDetunedToeplitz.lean`, and `EvenSectorPoleWeightUniqueness.lean`.

The constructive statement quantifies over arbitrary finite real coefficient sequences and produces an even, pole-free test realizing exactly their multiplicative correlations, with a positive common normalization. It has no positivity/source premise. The source classification concerns membership in the existing even cone and introduces no convergence, growth, sign, or Abel-limit assumption. It does not assert that the cone is inhabited; RH existence/positivity remains separate.

## Delivered mathematics and scope audit

- `RHTower.EvenSector.signed_arithmetic_evenization`: unconditional construction for every finite signed coefficient sequence, with exact samples at every positive and negative integer logarithmic node, including the origin.
- `RHTower.EvenSector.summable_abs_div_rpow_of_weilPositiveEvenPolar`: full absolute Dirichlet convergence is forced by the even pole-free cone, discharging the formerly open negative-superpole alternative.
- `RHTower.EvenSector.source_unique_of_weilPositiveEvenAt`: every source in every finite even pole-weight cone equals von Mangoldt on the actual arithmetic coordinates `n >= 2`.
- `RHTower.EvenSector.even_pole_weight_sources_subsingleton`: source uniqueness across the union of all finite pole weights.

The new structural operation enforces parity directly on arithmetic packets. Differences of centers retain the ratio grid; sums of centers are moved off every integer logarithmic node by a rational shift. This avoids the need to transfer signed positivity through the imaginary spectral segment. The internal energy estimate is used to close the source classification; it is not the terminal result.

Anti-theatre audit: no unproved analytic side condition was moved into the theorem statement. The realization is independent of any source or positivity assumption. No claim of positive-cone inhabitation or RH is made. No external novelty claim is made.

Anti-laziness audit: the conjecture loop continued past the failed pole-slack and multiplier shortcuts; the exact arithmetic construction was carried through convergence and source identification, rather than left at an intermediate lemma.

## Validation record

Targeted builds used `lake --old build GaloisForLFunctions.RHTower.EvenSectorPoleWeightUniqueness` and the new dependency targets during development. Final audits used `lake env lean GaloisForLFunctions/RHTower/<module>.lean` for each of the four new modules, sequentially. The `/tmp` scratch audit checked the imported API names and printed axioms for the exact packet identity, signed Toeplitz form, constructive realization, source identification, and source subsingleton theorem. No added axioms, placeholders, numerical experiments, or heartbeat overrides.

The repository-wide lint run failed only on unrelated umbrella reachability: `CHMDKleinGordonEnergyPositivityAndOriginMaximum`, `DeningerMeyerArithmeticSourceResolvent`, `DeningerMeyerArithmeticSymmetricSplitting`, `DeningerMeyerCausalConjugation`, `DeningerMeyerCausalReflectionCovariance`, `XiGaussianHeatBlockInertia`, and `XiGaussianHeatBlockJacobiCensus`. These were concurrent work outside this task's write scope and were left untouched. This records the lint result at audit time, not a claim that the entire shared repository is clean.

## Work discipline

Keep conjecturing after failed mechanisms. Complete a dependency-closed paper proof before adding a research Lean module. Use foreground targeted builds, one at a time; no full or umbrella builds, no numerical experiments, no heartbeat overrides. Leave concurrent work untouched.
