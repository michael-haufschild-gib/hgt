# Actual source factorization of a grid-preserving factorial producer

- **ID:** signed-prime-polar-factorial-source-factorization
- **Stage:** 1-in-progress
- **Type:** PAPER-PROVED / LEAN IN PROGRESS / UNCOUNTED
- **Scope:** Signed prime–polar transport; explicit actual-source producer.
- **Objective:** Construct explicit compact continuous real sources whose mixed
  correlation, or polarized autocorrelation difference, preserves the factorial
  prime-grid values and has an unconditional signed-pairing bound. Include actual
  source-energy costs and nonvanishing test size in the same package.

## Paper-proved mechanism, Lean endpoint pending

The continuous factorial test closes scalar continuity but is not an
autocorrelation: its origin is zero and its top value is two. A further
receiver or a formal polarization identity alone would not be a new contribution.
The missing step is an actual source construction with quantified cost.

For N≥1 set A=1+1/(4N), δ=log(A)/3, ε=exp(δ)−1. Construct the continuous
factorial ramp stencil R_N directly and set
ρ_N(t)=exp(t) max(0,min(t,2δ−t))/ε².
The explicit compact continuous sources are F_N(u)=R_N(−u) and
G_N(u)=exp(u/2)ρ_N(u). Their mixed correlation H_N preserves W_N(log n)
for every n≥1. The polar correction has coefficient [(1+exp(δ))/2]³.
Finite-rectangle Fubini and integer separation prove these statements on paper;
no rough triple-convolution regularity is assumed.

The sources F_N±G_N have equal origin energies in [6N,46N]. Their
autocorrelation difference divided by two is H_N(x)+H_N(−x), with squared
L² norm in [2,32] and the same positive-half-line signed pairing as H_N.
The bound is [10log(4N+1)+3+1/(4N)]/sqrt(N).
All arithmetic cancellation acts directly on T(N), in accordance with Trap 10
of the read-only `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`.

The shrinking collar can make source norms grow. Quantify this cost explicitly;
do not infer uniform packet control or positivity from scalar cancellation. Count
only a complete source construction, unconditional bound, size certificate, and
source-energy audit as one package.

## Search and next gates

`/tmp/spp9-next-search.json` is partial with interrupted text/source retrieval;
file coverage is a snapshot and compiler metadata is mostly source-only. Candidate
lemmas and source arguments were inspected. Retrieved precedents include
`exists_sourceTranslate_local_cross_zero` in `FiniteSourceEnergyScalarization.lean`,
`ChebyshevGauge.continuous_windowedTranslate`, the current factorial producer,
and `UnconditionalCoprimeFactorialLiftAndSpectralLaplaceProducer.lean`.
Their full scope must be inspected before code. Broaden the next documented
search to mathlib convolution continuity, associativity, support, and L² bounds.

- [x] Audit existing source-factorization and factorial-producer precedents.
- [x] Dependency-closed paper proof, including source-energy growth.
- [ ] Actual C_c sources and numeric-index-only public endpoint in Lean.
- [ ] Direct leaf checks, axioms, umbrella, lint and index.

The dependency-closed proof is now in
`docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialSourceFactorization.md`.
It constructs the initial ramp and exponential tent directly, avoiding rough
triple-convolution associativity. The actual autocorrelation contrast has exact
prime-grid values, an unconditional pairing bound and squared L² size in [2,32].
Both actual sources have equal origin energy in [6N,46N]. The complete Lean
endpoint remains pending; no part of the package is counted yet.

## Implementation checkpoint

The direct `ExponentialTentMoments.lean` leaf check passes with empty diagnostics
(`/tmp/spp10-tent-final.log`). The causal moment reuses the inspected bilateral
`HTGeometry.integral_tiltedTentFullProfile`; it is not a separate contribution.
`SignedPrimePolarSourceParameters.lean` also passes its final direct check
(`/tmp/spp10-parameters-final.log`). Source-energy proofs are staged in
`/tmp/spp10_tent_energy.lean`, positive/constant ramp moments in
`/tmp/spp10_ramp_moments.lean`, and the generalized ramp plus shifted grid lemma
in `/tmp/spp10_ramp_core.lean`. Those drafts are not certified yet.
The tent source-energy draft now passes in scratch form; its final leaf check
is running as `ExponentialTentSourceEnergy.lean`. The separate polar branch
moments and scalar atomic sum are drafted in `/tmp/spp10_ramp_pairing.lean`,
which depends on the two unchecked ramp drafts. The actual source contrast and
final arithmetic/energy endpoint still need Lean implementation. Main count
remains 9/100.

Searches `/tmp/spp10-convolution-search.json` and `/tmp/spp10-tent-search.json`
are partial (reranking deadline and semantic retrieval timeout respectively).
Available candidates and source arguments were inspected. The quadratic profile
in `integral_tent_mul_exp_interval` is not the required piecewise linear tent;
the bilateral linear-tent transform is applicable and reused.
