# Actual completed-Eisenstein RSZ normalization kill

- **ID:** C-A.9x
- **Stage:** 3-formalized
- **Type:** ROUTE KILL
- **Source:** `rh-current-frontier-map.md` HB survivor after C-A.9w
- **Statement:** The genuine parameter-family regularized triple moment of the actual completed Poincare legs is the classical four-`Lambda` family, not the corpus four-`XiC` canonical vertex; their forced nonconstant pole-fill ratio kills the surviving HB scalar-landing chain for the unmodified actual source.

## Goal

Close the surviving C-A.9w burden without replacing family regularization by a pointwise reporter.
Construct the literal meromorphic regularized scalar family from the actual completed Poincare
series, evaluate it, and compare its normalization with the canonical scalar vertex.

Exact RH chain tested:

`actual meromorphic scalar triple regularization -> claimed canonical four-Xi scalar landing ->
C-A.9u balanced source -> negative BM leg -> conserved left-QNM projection -> HC94 cocycle ->
Re(s)=1/2 on every Xi fibre -> RH`.

Hostile kill criterion: if the literal family equals the classical four-`Lambda` product, then the
already-proved nonzero factor-ten mismatch at `s=t=2` makes canonical scalar landing false and
retires this HB source normalization before any QNM work. A survivor must rescale the actual
Eisenstein source by the four elementary pole-fill factors before integration; post-specialization
finite-part modification is forbidden by C-A.9w.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact chain and kill witness fixed
- [x] 1 → 2 fully-proven: literal chamber source, complete paper proof, normalization comparison
- [x] 2 → 3 formalized: unconditional Lean theorem, direct Lean, targeted module build, axiom/lint audit
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, literature comparison

## Approach

1. Prove the full complex two-shift Ramanujan identity
   `sum sigma_a(n) sigma_b(n) n^(-w)` as the four-zeta quotient. This is the arithmetic collapse
   forced by the two nonzero Fourier modes after unfolding one actual Poincare leg.
2. Prove the Mellin integral of the product of two corpus `modifiedBesselKOrder` functions as the
   four-Gamma quotient on its exact absolute-convergence chamber.
3. Use the honest absolute-unfolding point `(P,Q)=(2,5)`, where `Re Q > 2 Re P`.  Unfold the
   `Q`-leg and substitute the certified actual Fourier coefficient, frequency pairing, and scaling
   `x=2πny`.  This removes every continuation and regularization ambiguity from the test.
4. Evaluate the literal source using 1–2 and the global xi functional equation.  It equals the
   classical four-`Lambda` value `Λ(8)Λ(5)^2Λ(-1)`.
5. Compare with `d4BMActualCanonicalScalarTripleVertex`.  Its four canonical factors are
   `28Λ(8)`, `10Λ(5)`, `10Λ(5)`, and `Λ(-1)`, so it is exactly `2800` times the nonzero literal
   source.  This single interior-chamber witness kills the claimed family equality directly.

Conjecture loop:

- C-A.9x-a: **LEAN-PROVED** full two-shift Ramanujan divisor-product identity, including absolute
  convergence and exact four-zeta quotient on the negative-shift chamber.
- C-A.9x-b: **LEAN-PROVED** exact complex two-`K` Mellin product identity on the sharp
  absolute-convergence chamber.
- C-A.9x-c: **LEAN-PROVED FOR THE POST-FOURIER SOURCE** at `(P,Q)=(2,5)`: the exact source equals
  the classical four-`Lambda` value, with no continuation.
- C-A.9x-d: **LEAN-PROVED SOURCE NORMALIZATION**: canonical vertex is exactly `2800` times the
  nonzero post-Fourier source.
- C-A.9x-e: **LEAN-PROVED ROUTE INCOMPATIBILITY**: analytic-family finite part annihilates every
  diagonal triple-Eisenstein constant-boundary family, for arbitrary eight Weyl-sector
  coefficients.  Hence every allowed source-compatible regularization remains the unfolded source,
  canonical remains exactly `2800` times it, and no actual finite-part reporter can satisfy both
  source compatibility and canonical landing.

Failure of any identity triggers correction of its exact normalization or chamber; it does not
authorize replacing the literal source, regularization, or integral by a prescribed scalar.

## Novelty and source audit

Zagier's regularized Rankin--Selberg method and the triple-Eisenstein formula quoted in
Djankovic--Khan give the classical four-completed-zeta family; Wu treats singular cases by
deformation. Corpus search finds the actual completed Poincare series, its exact Fourier
coefficients, the one-kernel Gamma--Bessel transform, and the one-Ramanujan-sum Dirichlet series,
but no two-shift divisor-product identity, two-`K` Mellin identity, literal family regularization,
or source-normalized comparison theorem. Novelty claim is the exact HB source-normalization kill
and its forced pre-integration pole-fill survivor, not the classical scalar formula by itself.

## No-go closure

- **Exact killing theorem/mechanism:**
  `d4BM_no_actualFinitePart_sourceCompatible_and_canonical_two_five`; closed nonexistence of a
  reporter on the literal truncated scalar moment satisfying both allowed analytic-family source
  compatibility and canonical HB landing.  The stronger boundary-class theorem
  `d4BM_no_diagonalBoundaryFamily_repairs_unfoldedSource_two_five` quantifies over all eight
  constant-boundary coefficient functions.
- **Strongest positive survivor:**
  `d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five`; exact source-level
  pole-fill multiplier `2800` at `(2,5)`.  Any replacement HB landing must insert its elementary
  pole-fill normalization before integration.
- **New insight:** an interior point with `Re Q > 2 Re P` is enough to test the family claim, so no
  several-variable continuation theorem is needed.  Pointwise regularization is impossible by
  C-A.9w, and analytic continuation cannot change an already false chamber identity.
- **Status:** unmodified source-compatible HB scalar-landing route killed; positive survivor
  Lean-proved.

## Log

- 2026-08-29 — created in 1-in-progress after corpus and primary-source audit.
- 2026-08-29 — C-A.9x-a closed in
  `ThetaCuspHawkingBMEisensteinRamanujanProductDirichletSeries.lean`.  Prime-local formal-series
  identity, multiplicative globalization, divisor-square convergence, and nonzero denominator
  cancellation are unconditional.  Remaining irreducible analytic gate is C-A.9x-b, the two-K
  Mellin product; no route conclusion claimed yet.
- 2026-08-29 — C-A.9x-b paper proof closed on the sharp absolute-convergence chamber
  `lambda.re > |mu.re| + |nu.re|`.  Put
  `J(lambda, alpha) = integral_R exp(alpha*r) cosh(r)^(-lambda) dr`.  The corpus logistic chart
  `v = exp(r)/(2*cosh(r))` has derivative `1/(2*cosh(r)^2)` and maps `R` bijectively to `(0,1)`.
  With `A=(lambda+alpha)/2`, `B=(lambda-alpha)/2`, its two logarithmic identities give exactly
  `v^(A-1)(1-v)^(B-1) dv = 2^(1-lambda) exp(alpha*r) cosh(r)^(-lambda) dr`.
  Since `A.re,B.re>0` iff `|alpha.re|<lambda.re`, Euler's complex Beta integral yields
  `J(lambda,alpha)=2^(lambda-1) Gamma(A) Gamma(B)/Gamma(lambda)`; the same chart proves absolute
  integrability after replacing parameters by their real parts.

  For `x>0`, reflection of the negative half-line and evenness of `cosh` give the absolutely
  convergent whole-line Schlaefli identity
  `integral_R exp(-x*cosh(t)+mu*t) dt = 2*K_x(mu)`.  Hence the requested Mellin integral is one
  quarter of the integral over `x>0` and `(t,u) in R^2` of
  `x^(lambda-1) exp(-x*(cosh(t)+cosh(u)) + mu*t + nu*u)`.  Absolute convergence follows by first
  integrating its norm in `x`: the corpus complex-rate Gamma integral reduces it to the positive
  plane kernel with parameters `(lambda.re,mu.re,nu.re)`.  Under the real-linear map
  `(p,q) |-> (p+q,p-q)`, whose determinant has absolute value `2`,
  `cosh(p+q)+cosh(p-q)=2*cosh(p)*cosh(q)` and the plane kernel factors as the product of
  `J(lambda,mu+nu)` and `J(lambda,mu-nu)`.  The chamber implies both Beta conditions because
  `|mu.re +/- nu.re| <= |mu.re|+|nu.re|`.

  Fubini is therefore justified.  Integrating `x` first gives `Gamma(lambda)` times the plane
  kernel.  Applying the determinant-two change and the two `J` evaluations gives
  `Gamma(lambda)/4 * 2 * 2^(-lambda) * J(lambda,mu+nu) * J(lambda,mu-nu)`.
  Cancelling the two copies of `Gamma(lambda)` (nonzero because `lambda.re>0`) proves
  `integral_0^infty x^(lambda-1) K_x(mu) K_x(nu) dx =
   2^(lambda-3)/Gamma(lambda) *
   Gamma((lambda+mu+nu)/2) Gamma((lambda+mu-nu)/2)
   Gamma((lambda-mu+nu)/2) Gamma((lambda-mu-nu)/2)`.
  Hostile checks of all four Gamma arguments reduce to the same chamber; no continuation or
  unproved boundary interchange is used.  Status: **PAPER-PROVED**; exact Lean formalization active.
- 2026-08-29 — C-A.9x-b closed in
  `ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct.lean`.  The formal theorem
  `integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder` proves the full complex
  four-Gamma formula under `|Re mu| + |Re nu| < Re s`.  Lean also forced and verified the stronger
  infrastructure: full complex hyperbolic Beta transform, determinant-two plane separation,
  invertible-linear-map transport of absolute convergence, whole-line exponential Schlaefli
  representation, and exact norm evaluation closing the three-variable Fubini passage.  Direct
  `lake env lean` passed.  Status: **LEAN-PROVED**.  Remaining route-kill gate is C-A.9x-c/d, the
  literal actual-family unfolding and its comparison with the canonical four-`XiC` vertex.
- 2026-08-29 — C-A.9x-c/d closed at the sharper interior witness `(P,Q)=(2,5)`.  The production
  module `ThetaCuspHawkingBMEisensteinActualUnfoldedScalarNormalizationNoGo.lean` identifies the
  actual Whittaker coefficient with the generalized-divisor arithmetic, evaluates the exact
  post-Fourier/post-scaling source using the Ramanujan and two-K theorems, and welds `Λ(-1)=Λ(2)`
  via the global xi functional equation.  It proves the source equals the classical RSZ value,
  proves it nonzero, proves the canonical vertex equals exactly `2800` times it, and derives the
  closed source-normalization no-go theorem.  Hostile post-audit found that the corpus still lacks
  the theorem identifying analytic-family finite part of the actual truncated scalar moment with
  this post-Fourier source.  Status: **C-A.9x-c/d LEAN-PROVED; ROUTE KILL WITHHELD PENDING C-A.9x-e**.
- 2026-08-29 — audit: direct `lake env lean` and targeted `lake build` of the production module
  passed.  `#print axioms` on source evaluation, exact-ratio survivor, and no-go theorem reports
  only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide `formal_tools.py lint`
  was invoked; it reports unrelated pre-existing unreachable modules in the RHTower and HTGeometry
  umbrellas, while this new module is wired and absent from every lint error.
- 2026-08-29 — hostile C-A.9x-e pivot closed the last logical escape.  Corpus analytic-family
  finite-part rigidity annihilates the entire diagonal triple-Eisenstein boundary class, regardless
  of its eight coefficient functions.  The module now proves canonical is `2800` times every such
  regularized value, proves no boundary family repairs the mismatch, and proves closed nonexistence
  of an actual truncated-moment finite-part reporter that is simultaneously source-compatible and
  canonical.  This kills the unmodified source-compatible family-level HB scalar landing without
  assuming existence of a particular reporter.  Final direct Lean, targeted module build, and
  foundation-only axiom audit passed.
