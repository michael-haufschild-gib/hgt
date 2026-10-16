# FU: common preparation of a prescribed finite prime cube

New directly checked Lean result: `formal/GaloisForLFunctions/RHTower/MobiusDivisorPreparedPrimeCube.lean`.

`exists_mobiusDivisorPreparedPrimeCube`: for any nonempty inherited finite prime core P and disjoint finite target prime block T, there is W>0 such that for every lower prime bound B one actual finite prime helper set S, disjoint from P union T and with all primes>B and inverse-square-root mass<=W, makes every nonempty alternating Boolean energy difference positive at every intermediate target subset. All vertices and all difference orders share one eventual tail of original integer energies. Limiting coefficients are also strictly positive. Targets are prescribed BEFORE helpers; W is fixed BEFORE B.

`mobiusDivisorPreparedPrimeCube_unconditional` is a closed theorem over finite sets of Nat.Primes; it anchors inherited source at 2 and removes inherited targets. No unpaid analytic or RH hypothesis.

Dependencies: `MobiusDivisorPrimeClusterSynthesis.lean` builds disjoint actual prime windows of equal inverse-square-root mass; `MobiusDivisorPrimePhaseGate.lean` proves common positivity for finite compatible signed tests; `MobiusDivisorBooleanEnergySpectrum.lean` proves exact all-order cosine-product identity. Reusable helpers in `MobiusDivisorInheritedPrimeInsertionProducer.lean` now belong to `RHTower.PrimePreparation`; existing public theorem statements unchanged. Four new modules wired into RHTower umbrella.

Mechanism: R={1} union T, k=card R. A bad target cosine forces the common phasor sum above -(k-2+sqrt 2), while a periodic gate in a small neighborhood of t=0 accesses exponent rate arbitrarily near k. Quantized fast carrier frequencies preserve the exact gate mean. Equal-mass actual prime clusters approximate this exponential with one global integrable domination. Apply to all tests w_(P union A)(t) product_(p in D) cos(t log p). Density-normalized Euler factors are exactly 1-(2 sqrt p/(p+1))cos(t log p).

IMPORTANT boundary: this solves finite prescribed all-order sign compatibility, NOT net helper repayment or an exhaustive moving-core schedule. It does not assert kappa(P union S)<=kappa(P). The known adverse mixed-pair theorem chooses primes AFTER a fixed core, so is consistent. Do not infer a cofinal/infinite preparation from this finite theorem.

All affected leaves checked with foreground `lake --old env lean`, no full builds, numerical experiments or heartbeat changes. Axiom audit of six public results returned only propext, Classical.choice, Quot.sound. Full formal lint snapshot failed solely on eleven unrelated unwired concurrent theta/Suzuki modules; no FU reachability or forbidden-declaration errors. Full output /tmp/fu-final-lint.log.

Paper proof, conjecture ledger, exact theorem and validation: `docs/drafts/pipeline/3-formalized/fu-prescribed-prime-complete-monotonicity.md`. FU frontier-map section updated. No web or external novelty audit performed.