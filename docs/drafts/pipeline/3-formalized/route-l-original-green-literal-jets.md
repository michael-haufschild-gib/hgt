# Route L: literal original Green jet readers

- **ID:** RH-L-C54
- **Stage:** 3-formalized
- **Type:** literal integral admission, derivative identification, and prefix convergence
- **Source:** Route L; C53 full-source reader investigation
- **Statement:** Identify every native Mellin jet of the literal complete original-prime Green source with its analytic Euler-quotient derivative, with absolute integral admission proved first.

## Why this is in the proof chain

The ultimate chain remains complete original source → fixed physical-reader agreement → conormal vanishing → RH. C53 did not establish the selected cyclic/physical comparison. The existing original Green module proves analyticity and derivatives of its Mellin transform, but only the zeroth literal Green integral is admitted there. The underlying damped source has all literal jets; its future Green sum is a different function and needs its own integral-domain proof before the derivative reader can be identified with the actual source jet reader. This is an analytic dependency, not cyclicity or RH.

## Dependency-closed paper argument

For a function whose zeroth Mellin integrals are absolutely admitted in an open strip, choose two real weights on opposite sides of the selected real part. The corpus inequality `deninger_abs_pow_exp_le_two_weights` controls each finite polynomial moment by the sum of those two admitted weights. This gives absolute admission at every finite order. The same bounds at order k+1 dominate the parameter derivative uniformly on a smaller complex ball, so differentiation under the integral identifies consecutive jets. Induction gives every iterated derivative.

Apply the lemma to the unchanged original future Green sum. Its proved admission strip is `max(0,1-a) < Re(s) < a`; no boundary subtraction is introduced. Its known Mellin identity then gives the full Euler quotient with the original prime denominator. At damping one every original Xi support point is admitted, independently of multiplicity; use the actual native order, not a fixed upper bound.

For finite-prime sources, the same original future Green sum admits every jet in `Re(s)>0`. Write its Mellin transform as `M_N(s) D_p(s)`, with the fixed analytic multiplier `D_p(s)=(1-exp(-s log p))^(-1)`. At fixed order k, Leibniz gives the finite sum

`sum_(i=0)^k choose(k,i) M_N^(i)(s) D_p^(k-i)(s)`.

C45 proves convergence of each original source derivative `M_N^(i)(s)` to the derivative of the full source. Passing through this finite sum proves convergence of the actual Green jet integrals. This argument retains all derivatives of the original prime multiplier. It supplies no bound uniform in k or over the complete Xi divisor.

## Earlier attempts checked this turn

The exact internal Green covariance law cancels two generally nonzero factors; it does not annihilate them separately. The original `xiGaussianGammaResidueNormalizer` and packet contain Gaussian, Gamma and rational factors, but neither contains the first surviving zeta jets. Their product is exactly one, so they do not cancel C52's inverse-zeta-jet factors. No zero-damping full-Xi norm admission follows from that normalization.

Broad arXiv search `interpolation` returned Xing Li, [Sharp Concave-Function Transfer for Lee-Type Schatten Norm Inequalities](https://arxiv.org/html/2608.25989v1), August 26, 2026. Its Theorem 1.1 bounds the transformed norm of a sum above by the sum of transformed absolute values. Applying it to opposite covariance defects does not bound the component norms by zero; that would require the reverse inequality. Its weighted positive-map lemma requires a source density obtained from the actual adjoint map; no such density comparison was constructed here. No paper computation was used.


A second broad newest-first search, `reciprocity`, found Camacho et al., [Temporal Localisation of Waves from Imaginary Line-Gap Topology](https://arxiv.org/html/2609.11577v1), September 10, 2026. Equations (1)–(2) allow the particle-hole-symmetric matrix with off-diagonal entries z for arbitrary complex z; its eigenvalues are z and -z. Thus that symmetry does not itself supply a real spectrum. Their phase-switching argument gives decay for a finite interval under a specified initial-overlap condition; the paper explicitly allows later renewed growth. Tested transfer: a reflected source pair would still need a source-derived phase path and the correct overlap condition, and finite-interval decay would not annihilate the retained boundary coefficient. No such path or comparison was obtained. This is an applicability check of the symbolic argument, not use of its numerical simulations.

## Corpus audit

Two deep searches ran against the whole configured corpus with `--any` and source/method retrieval. Every returned candidate and method statement/assumption was inspected (20 candidates and 20 source arguments per search).

- `route-l-source-equation-comparison-search.json`: query generation 879253, coverage snapshot 879257/current 879258; 57,044 files indexed, 707,270 method records ready, 1,011 stale. Partial interrupted boundary/IBP retrieval. The boundary-to-area ingredient group supplies generic integration identities but no identification or annihilation of the selected source.
- `route-l-original-green-literal-jet-search.json`: generation 879260; coverage pending, partial at the deadline/reranking. No proof ideas or ingredient sets returned. Exact useful hits were C45's source jet admission/error bound, the strong-log jet norm identity, and the zeroth weighted-source admission. Strong-log decay and Cauchy-kernel results have different domains. Definitions returned as methods were not treated as proofs.

The admitted-source methods were reused and generalized to an open strip. Partial search does not establish absence of another corpus proof.

## Status

Ten public theorems are closed in `formal/GaloisForLFunctions/RHTower/Deninger/DeningerDampedOriginalGreenMellinJets.lean`:

- Open-strip admission of all finite literal jets, differentiation under the integral, and iterated derivative identification.
- The original full Green source's jet admission, literal/analytic identity, and full Euler-quotient identity.
- Unconditional admission/identity at every Xi support point and every finite order at damping one.
- Finite-source Green jet admission and derivative identification in the right half-plane.
- Convergence of every actual finite-prime Green jet integral to the full original source integral.

Validation on September 12, 2026:

- `lake env lean /tmp/route_l_original_green_jets.lean`: exit 0.
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerDampedOriginalGreenMellinJets`: exit 0; new leaf compiled in 4.4 seconds, dependency output replayed from cache.
- `scripts/formal_tools.py index`: exit 0; refreshed seven changed source records.
- Module wired once into `GaloisForLFunctions/RHTower.lean`; no umbrella build.
- Default Lean limits; no added axioms, unfinished proof placeholders, numerical experiments, or axiom-print audit.
- Repository lint: exit 1, reporting seven unrelated modules unreachable from their umbrellas: `ThetaCuspHawkingBMHorizonModeOuterUniformBound`, `ThetaCuspHawkingBMTemporalCurrentClearedDensity`, `ThetaCuspHawkingBMTemporalCurrentClearedDensityBound`, `ThetaCuspHawkingBMTemporalCurrentRadialCutoff`, `ThetaCuspHawkingBMTemporalCurrentRadialPackage`, `JetCoefficientUniqueness`, and `SecondEndpointMellinLaurentInterchange`. No error named this module. These are concurrent work outside this card's scope.

The fixed cyclic-source/physical boundary agreement remains UNPROVED. The new result closes the literal derivative and prefix-limit comparison, not the physical annihilation. It provides no all-order full-Xi norm estimate and no zero-damping source passage. Next mathematical target remains an independent source identity for the selected complete physical boundary with its original horizontal anchor; neither this analytic identity nor the two literature tests supplies one. Existing route-independent ledger requirements already cover the distinction between finite-order admission and combined completion; no new universal constraint is asserted.
