# JAS prime-Haar prefix Cauchy reflection discriminator

Status: FORMALIZED IN LEAN
Route: JAS
Date: 2026-08-29
Labels: `[PROVED IN LEAN]` `[CORPUS-NOVEL ROUTE THEOREM]` `[TARGETED EXTERNAL NO-MATCH]` `[GLOBAL NOVELTY UNVERIFIED]`

## Result

For arbitrary natural-index circle-Poisson parameters `a,b`, the canonical prefix square-root
likelihood sequence is Cauchy in `L²(product b)` exactly when the local Hellinger defects

`1 - circlePoissonHellingerAffinity (a n) (b n)`

are summable.  For the prime-Poisson family compared with Haar, this gives the sharp structural
wall

`CauchySeq (primePoissonHaarPrefixHalfLikelihoodLp sigma t hsigma) ↔ 1 / 2 < sigma`.

At an actual Xi-divisor point `rho`, forward/reflected Cauchy coherence is therefore equivalent to
`Re rho = 1/2`.  Universal coherence over the Xi divisor is equivalent to RH.

Formal module:
`formal/GaloisForLFunctions/RHTower/JointAncestryPrimeHaarPrefixCauchyReflectionDiscriminator.lean`

Capstones:

- `cauchySeq_circlePoissonPrefixHalfLikelihoodLp_iff`
- `cauchySeq_primePoissonHaarPrefixHalfLikelihoodLp_iff`
- `xiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff`
- `everyXiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff_riemannHypothesis`

## Corpus origin

Conjecture was frozen only after mandatory `scripts/formal_tools.py research` searches for prefix
half-likelihoods, Hellinger tail products, the prime-Poisson/Haar Kakutani wall, Xi-divisor
reflection, and Gamma-theta cross-aperture transport.  Corpus supplied:

- `circlePoissonPrefixHalfLikelihoodLp`;
- `norm_sq_prefixHalfLikelihoodLp_sub`;
- the previously one-way theorem `cauchySeq_circlePoissonPrefixHalfLikelihoodLp`;
- `tendsto_circlePoissonPrefixAffinity_zero_of_not_summable`;
- `summable_normSq_primePoissonParameter_zero_iff`;
- `summable_hellinger_primePoissonNaturalParameters`;
- `riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half`.

No corpus theorem stated the Cauchy converse, sharp prime specialization, or reflection-Cauchy Xi
classifier.

## Proof

For the generic converse, assume Hellinger defects are nonsummable.  Every finite deletion remains
nonsummable.  Shift beyond an arbitrary proposed Cauchy tail start and use vanishing shifted prefix
affinity to choose a later endpoint with interval affinity below `1/2`.  The exact norm-square
identity makes the corresponding vector distance exceed `1`, contradicting Cauchy.

For prime-Poisson parameters, the corpus quadratic lower bound converts summable Hellinger defects
to square-summable prime parameters.  Reindexing by `natEquivPrimes` and the exact prime wall forces
`sigma > 1/2`; the converse follows from existing Hellinger summability.  Applying the threshold to
`sigma` and `1-sigma`, then using the open critical strip, proves reflection coherence iff
`sigma = 1/2`.

## Exact RH chain and remaining producer

1. Prefix Cauchy iff Hellinger-defect summability — proved here.
2. Prime/Haar prefix Cauchy iff `sigma > 1/2` — proved here.
3. Completed Gamma-theta functional-equation transport must preserve Cauchy status between
   `sigma` and `1-sigma` at every Xi divisor — open producer.
4. Steps 2--3 force `sigma = 1/2` at every Xi divisor.
5. `riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half` concludes RH.

This module closes the discriminator and classifies the exact producer needed.  It does not prove
the producer or RH.  Finite-packet identities cannot discharge step 3; required datum is an
infinite-support reflection transport with uniform two-sided conditioning along the cofinal prime
prefixes.

## Novelty audit

Classical Kakutani theory covers equivalence/singularity of countable products, and Poisson-process
literature relates Bhattacharyya/Hellinger distances to intensity measures.  These classical
ingredients are not claimed novel.  Targeted searches found no paper stating this exact
prime-Poisson prefix-Cauchy discriminator, its Xi-reflection classifier, or its RH equivalence.
Relevant comparisons:

- https://arxiv.org/abs/1611.10289
- https://arxiv.org/abs/1312.6224
- https://arxiv.org/abs/1509.03643
- https://arxiv.org/abs/2206.02612

## Audit

- `lake env lean GaloisForLFunctions/RHTower/JointAncestryPrimeHaarPrefixCauchyReflectionDiscriminator.lean` — passed, no diagnostics.
- `lake build GaloisForLFunctions.RHTower.JointAncestryPrimeHaarPrefixCauchyReflectionDiscriminator` — passed (`12198/12198`).
- `#print axioms` on all four capstones — only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint found no forbidden declaration in the module; repository-wide failure consists of
  pre-existing unrelated reachability errors and large-file warnings.
- Module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.
