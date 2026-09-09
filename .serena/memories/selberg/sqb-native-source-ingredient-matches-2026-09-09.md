# SQB source ingredient matches (SQB41)

Active RH goal remains unproved. No numerical computations, frontier-map edits, new Lean modules, or umbrella edits in SQB41. Current card: `docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md`. This turn found existing ingredients; it did NOT prove a new native residual estimate. Do not report it as an RH proof or a new mathematical theorem.

Full chain: literal theta source -> normalized packets with vanishing full native residual -> entire Xi occurrence -> critical line -> RH. Hardest target remains source cancellation/reality of the corrected scalar response from SQB39, beyond SQB40's exact signed quadrature formula.

## Avoid rebuilding existing producers
- `HedenmalmThetaSourceSpectrumExact.lean`, namespace `RHTower.HedenmalmThetaSource`: `integrable_thetaCuspFourierLaplaceIntegrand_all` line139 and `thetaCuspFourierLaplace_eq_XiC_all` line264 already cover ALL complex parameters. Initial `ThetaCuspFourierLaplace.lean` has an older strip-only result. Exhaustive reference search found the existing upgrade.
- `ThetaTailFirstMomentKreinTransform.lean`: `integrable_thetaBilateralLaplace`, `thetaBilateralLaplace_eq_XiC`. Literal all-complex source Laplace transform already closed.
- `SelbergThetaTotientHankel.transform_kernel` line324: full signed arithmetic/completed-zeta transform admitted in its safe half-plane. Its input is a dyadic tilted-profile Hankel correlation, NOT SQB36 common-forcing p_q. `kernel_mean_abel_limit` line494 is at the mean pole, NOT native real-frequency Plancherel.
- `XiCTaylorThetaTailMobiusConstraint.thetaCuspTailSecondDensityAtom_one_eq_tsum_moebius_translate` line316 gives absolute critical inversion for x>=0; preserve source/half-power weights and domain.
- `DeletionMixedRefinement.norm_unitFullFourierSource_even_le` gives actual Bernoulli even-reflection bound <= displacement^2/6. Different source/measure. Downstream Hardy floor gives selected zero-free segments, not all heights.
- `Sieve.eventually_norm_sum_moebiusTwist_div_lt` is uniform o(N) for its explicit growing twist range, not square-root cancellation.

Eight interfaces checked in `/tmp/sqb41_retrieved_interfaces.lean` with `lake env lean` exit0. Six substantive #print axioms results in `/tmp/sqb41_retrieved_interfaces.log` use only propext, Classical.choice, Quot.sound. All owned Lean/search sessions terminal.

## Analytical candidate, NOT Lean proved
Write Phi=full theta source, f(y)=sqrt(y)Phi(log(y)/2), J=actual positive horizontal mean, g=SQB40 radialProjection. Proposed safe Mellin formula:
 integral_0^infinity a^(z-1) J(a^2) da = xi(z+3/2)*(1+Lambda(z+1)/Lambda(z+2)), Re z>0.
Full Phi Laplace is already known; remaining joins radial projection, complete row interchange, spectral boundary. Main residue candidate C=6 xi(3/2)/pi=LB; equality C=M/V requires actual native volume/mass normalization.
For k(x)=exp(-x)*(J(exp(2x))-C), proposed even real-frequency multiplier is XiC(t)*w(t), w=1+Re(conj Lambda(1+it)/Lambda(1+it)), hence 0<=w<=2 off0. Functional equation yields this symbol algebraically, but actual boundary admission is OPEN.
Proposed m(q)=1/(4pi) integral XiC(t)^2 w(t)/(t^2-z_q^2) dt. Its imaginary sign AGREES with existing native self-adjoint Gram law. Positivity/upper norm comparison alone does NOT force m(q) real or prove RH. Do not spend a turn presenting this bound as the missing orientation or formalize it merely as padding.

## Retrieval state
Broad OR queries used theta/divisor/Mellin/radial; theta/Mobius/Poisson; signed/quadrature; scattering/Plancherel/contraction; intertwining/source/coercivity/spectral/cancellation; common/forcing/resolvent/oriented/imaginary/boundary; theta/reflection/positivity/total; moebius/cancellation; Mertens/Tauberian/remainder.
Deep intertwining output `/tmp/sqb41_deep_intertwining.json` retained 25 candidates +25 source arguments but partial=true, interrupted text/source retrieval, vector deadline, pending coverage, no proof_ideas/ingredient_sets. No absence conclusion justified. Source domains and measures must be checked, not just result names. Separate peer owns ongoing search-upgrade/background indexer; preserve their files/processes.
