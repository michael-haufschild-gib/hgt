# Actual source factorization of a grid-preserving factorial producer

- **ID:** signed-prime-polar-factorial-source-factorization
- **Stage:** 1-in-progress
- **Type:** PAPER-PROVED / LEAN IN PROGRESS / UNCOUNTED
- **Scope:** Signed prime–polar transport; explicit actual-source producer.
- **Objective:** Construct explicit compact continuous real sources whose mixed
  correlation, or polarized autocorrelation difference, preserves the factorial
  prime-grid values and has an unconditional signed-pairing bound. Include actual
  source-energy costs and nonvanishing test size in the same package.

## Candidate mechanism, not yet audited

The continuous factorial test closes scalar continuity but is not an
autocorrelation: its origin is zero and its top value is two. A further
receiver or a formal polarization identity alone would not be a new contribution.
The missing step is an actual source construction with quantified cost.

For N≥1 let W_N be the verified discontinuous factorial bi-null test. Set
A=1+1/(4N), δ=log(A)/3 and
k(t)=exp(3t/2) 1_[0,δ](t)/(exp(δ)−1).
Consider the causal triple convolution H_N=W_N*k*k*k. A change of variables
λ_i=exp(t_i) suggests that H_N is the average of the common-dilation tests
W_N^λ with λ=λ₁λ₂λ₃≤A. Thus exact grid preservation should survive, and the
polar correction should involve the explicit mean dilation
[(1+exp(δ))/2]^3. Both assertions require a full endpoint and Fubini audit.

Potential actual sources are F_N(u)=(W_N*k)(−u) and G_N(u)=(k*k)(u).
Their mixed correlation should be H_N. Their supports lie on opposite half-lines,
so the autocorrelations of F_N+G_N and F_N−G_N should have equal origin energies;
their difference on the positive half-line should be 2H_N. Check the correlation
orientation and factor two explicitly. Derive continuity from genuine convolution
integrability, not from a claimed regularity of the discontinuous ingredients.

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
Both actual sources have equal origin energy in [6N,46N]. All Lean verification
remains pending; no part of the package is counted yet.

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
