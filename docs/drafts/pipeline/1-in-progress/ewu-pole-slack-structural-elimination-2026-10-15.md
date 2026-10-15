# EWU: structural elimination of pole slack

Status: in progress. Evidence source: current Lean corpus only. No external search or novelty audit, per user instruction.

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
4. For a source positive at any finite pole weight, the already-audited `canonical_of_weilPositiveEvenAt_of_absolute_convergence` now applies with convergence proved, not assumed. Thus the source is exactly von Mangoldt on `n>=2`. This eliminates the remaining superpole branch rather than reformulating it as a receiver.

Attack checks: the rational shift depends on `N`, but its required inverse width is polynomial, so the archimedean cost stays logarithmic. Every reflected node is excluded, not sampled. The profile is already polar-free, so changing its position introduces no pole slack. The source coefficients need no assumed sign or growth. Search found no existing version of this arithmetic reflection cancellation; search compiler metadata was largely source-only, so all dependencies will be checked by Lean.

Formalization pending; no theorem claimed yet.

## Work discipline

Keep conjecturing after failed mechanisms. Complete a dependency-closed paper proof before adding a research Lean module. Use foreground targeted builds, one at a time; no full or umbrella builds, no numerical experiments, no heartbeat overrides. Leave concurrent work untouched.
