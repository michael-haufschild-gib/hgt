# Actual source factorization of a grid-preserving factorial producer

- **ID:** signed-prime-polar-factorial-source-factorization
- **Stage:** 0-backlog
- **Type:** CANDIDATE / UNCOUNTED
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

- [ ] Audit existing source-factorization and factorial-producer precedents.
- [ ] Dependency-closed paper proof, including source-energy growth.
- [ ] Actual C_c sources and numeric-index-only public endpoint in Lean.
- [ ] Direct leaf checks, axioms, umbrella, lint and index.

No part of this candidate is counted or claimed formalized.
