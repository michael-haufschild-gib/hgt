# FZZ-P: match the continued plane integral to original cutoffs

Status: original whole-plane cutoff limit, source analyticity, Gamma-continuation equality and negative finite-part sign formalized, 2026-09-11. New Gamma leaf build and all four axiom audits passed; repository lint currently fails on unrelated missing umbrella imports. RH remains unproved.

## Chain and obstacle

Original complete FZZ source → integrated Ward identity in an independently fixed phase frame → balanced vacuum delay → passivity → RH. The ordinary plane Gamma identity and its original all-order logarithmic marks are now formalized. Physical exponents remain outside that chamber. The actual two-puncture cutoff finite part is now matched to the Gamma continuation. The original marked derivative with all counterterms retained and its Gamma response are now proved in the continued marked-source card. The diagonal response has a proved positive normalized lower bound and a strictly negative actual mark. The original differentiated independent-cutoff limit is now proved in the continued marked-source card. Higher collision subtractions and complete physical parameter transport remain open.

## Precise target

Write `K(a,b,z)=|z|^(-2a)|z-1|^(-2b)`, `R=1/2`, and let `E(a,b)` be the integral outside the two open radius-`R` disks. For `0<a,b<3/2`, `a+b>1`, define

- `A0(a,b)=integral_(|z|<R) |z|^(-2a)(|z-1|^(-2b)-1)`;
- `A1(a,b)=integral_(|z-1|<R) |z-1|^(-2b)(|z|^(-2a)-1)`;
- for `a,b != 1`, `FP=E+A0+A1+pi*R^(2-2a)/(1-a)+pi*R^(2-2b)/(1-b)`.

The local collision module proves admission of `A0,A1`. The exterior admission and complete original cutoff assembly are now formalized: the two radii may shrink independently, and the exact two local power counterterms give `FP` for `1<a,b<3/2`. Equal-radius removal follows by composition. Equality of this `FP` with the Gamma ratio and its strict negative sign are now proved in the new Gamma-continuation module.

## Conjecture → closed Gamma identity

Clear the two collision poles *in the definition*:

`H=(1-a)(1-b)(E+A0+A1)+pi(1-b)R^(2-2a)+pi(1-a)R^(2-2b)`.

Do not define this across the poles by multiplying a totalized singular quotient. Separate real analyticity of this explicitly cleared source is now proved; the [source-analytic audit](fzz-p-subtracted-screening-analytic.md) uses `alpha=-2a,beta=-2b` and a clearing normalization four times this one. The proposed Gamma partner is

`pi*Gamma(a+b-1)*Gamma(2-a)*Gamma(2-b)/(Gamma(a)*Gamma(b)*Gamma(2-a-b))`.

Reciprocal Gamma must be treated as an analytic function across `a+b=2`. Equality on the ordinary chamber and then two one-variable identity-theorem arguments identify these families. Division is performed only away from `a=1,b=1`, giving the proved original cutoff limit with the exact Gamma value.

Source analyticity is closed by splitting signed exponential weights, proving the original local and exterior integrability intervals, and replacing the variable-endpoint primitive by the exact fixed-interval identity `exp(aX)-1=a*integral_0^1 X*exp(a*t*X)dt`. The logarithmic weight and the product integral are admitted before Fubini. Both analytic slices, reflection, pole values and equality with the original finite part after clearing have passed all audits. Equality with the Gamma partner is now proved by the two connected analytic slices.

The sign conjecture is now proved: both exponents in `(1,3/2)` give a strictly negative finite part. Gamma recurrence moves the numerator factors to positive arguments; the remaining reciprocal Gamma factor has argument in `(-1,0)` and is negative. The original cutoff integrand is nonnegative. Thus positivity does not survive this forced subtraction. This concerns the position sector, not positivity or unitarity of a complete CFT correlator.

## Work plan

- [x] Exterior integrability and original two-cutoff limit, including independent radii; four public theorems fully audited.
- [x] Separate analyticity of the explicitly pole-cleared source, both slice directions, exact pole values and original finite-part relation; seven public theorems fully audited.
- [x] Analytic Gamma partner, identity-theorem match, negative finite-part sign and independent original Gamma cutoff limit; four public theorems passed scratch and leaf build.
- [x] Original continued marked derivative, its explicit local counterterm derivative and evaluated Gamma response; four public theorems passed scratch, leaf build and axiom audits. The differentiated independent-cutoff limit is now proved in the continued marked-source card.
- [x] Three leaf proofs, all ten public axiom checks and route updates.
- [ ] Shared-tree lint gate; latest failures are missing umbrella imports outside FZZ.

Higher Taylor subtractions, moving or coalescing punctures, higher screening depths, physical coupling/momentum identification and the complete Ward producer remain outside this first continuation strip.

## Current search evidence

`/tmp/fzzp-plane-finitepart-analytic-methods.json`: partial generation 823289; malformed local-model judgment and deadline, with predominantly irrelevant Hadamard-matrix methods. All returned names were inspected; no source-continuation theorem was supplied. Rephrased reciprocal-Gamma deep/method search: `/tmp/fzzp-plane-reciprocal-gamma-methods.json`. Source text already locates mathlib's `differentiable_one_div_Gamma`; applicability remains to be checked in scratch. This is a plan, not a proof certificate.


The rephrased reciprocal-Gamma search returned partial generation 823293 with complete file inventory but incomplete source/compiler and semantic coverage; all candidate/method names and the proposed ingredient set were inspected. `Complex.differentiable_one_div_Gamma` in mathlib `Gamma/Beta.lean` is an unconditional entire-reciprocal theorem. `/tmp/fzzp_plane_continuation_names.lean` now verifies its use and proves, in scratch, `AnalyticAt ℝ (fun s : ℝ => (Real.Gamma s)⁻¹) r` for every real `r`, by restricting the complex analytic function. Log `/tmp/fzzp-plane-continuation-names.log` is clean. Required real-part restriction import: `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`. The unrelated `Gammaℝ` symbol in `ZetaCarrier` is an archimedean completed Gamma factor and must not be substituted for `Real.Gamma`.

This verifies the reciprocal-Gamma component of the proposed partner. At that checkpoint source analyticity and whole-plane cutoff assembly were open; both have since been proved as recorded below.


## Audited original global cutoff result

`formal/GaloisForLFunctions/RHTower/FZZCigarPlaneScreeningCutoff.lean` proves:

1. Exterior integrability whenever `alpha+beta<-2`, using a positive chart in the public statement. For `|z|>2`, the retained two-factor kernel is bounded by a constant times `|z|^(alpha+beta)`; the remaining exterior region is compact and avoids both punctures.
2. Ordinary integrability of every positive pair of original cutoff domains in the first continuation strip.
3. Exact decomposition into both local annuli and the unchanged exterior; the open half-radius collision disks are disjoint.
4. Independent cutoff convergence in the product filter `atTop ×ˢ atTop`, for `epsilon0=exp(-T)` and `epsilon1=exp(-U)`, with the exact counterterms `2*pi*epsilon0^(alpha+2)/(alpha+2)` and `2*pi*epsilon1^(beta+2)/(beta+2)`. The limit is both local finite parts plus the exterior. The equal-radius limit is a corollary.

Public exponents are `fzzScreeningFirstContinuationPower u,v`, each in `(-3,-2)`. The Gamma match is now proved below; the first original exponent derivative and its Gamma response are now proved in the continued marked-source card. The independent-cutoff derivative interchange is now proved there. Higher collision subtractions, a full CFT deformation, the independent frame and the mixed Ward producer remain separate obligations.

Validation: `/tmp/fzzp_plane_cutoff.lean` clean scratch pass; leaf-only `lake build GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningCutoff` passed (8837 dependency jobs, leaf 58 seconds); all four public theorem axiom closures contain only `propext`, `Classical.choice`, `Quot.sound`; formal lint passed. Logs: `/tmp/fzzp-plane-cutoff-{scratch,build,axioms,lint}.log`. Module is wired into `GaloisForLFunctions.RHTower`; no umbrella build was run.

## Next conjecture → proof attack

The analytic-primitive search did not provide a ready original-source theorem. A more concrete replacement is the exact fixed-interval identity

`exp(a*X)-1 = a * integral_(0,1) X*exp(a*t*X) dt`.

On the collision disk at one, `X=log|z|` is bounded and vanishes linearly at the puncture. Thus `|z-1|^beta*X` is integrable for `beta>-3`. Lift the original subtraction to this fixed interval, establish joint integrability, and split its signed weight into positive and negative parts. Each resulting moment-generating function has an open exponential-moment domain; its analyticity then comes from the source itself. This avoids assuming analyticity of a primitive or of the desired Gamma expression. This construction is now formalized and fully audited in [the subtracted-source card](fzz-p-subtracted-screening-analytic.md). The completed scratch `/tmp/fzzp_plane_gamma_match.lean` now proves the Gamma partner, ordinary-chamber cancellation and both identity-theorem extensions.

With both local directions and the exterior now proved analytic, the explicit pole-cleared source can be matched in two connected one-variable slices: first keep `0<b<1` and extend in `a`; then keep the extended `a` and extend in `b`. The ordinary chamber supplies a nonempty open equality interval in each slice. Reciprocal Gamma is analytic through `a+b=2`, as already checked above.

Search: `/tmp/fzzp-plane-holomorphic-subtraction-methods.json` returned partial generation 823299 with incomplete semantic/source/compiler coverage and deadline; all 20 candidate and 20 method names were inspected. The generated ingredient set was unverified and did not supply the match. The applicable source method is `HTGeometry.coordDivQuotient_differentiableAt` in `HolomorphicCoordinateDivision.lean`: a fixed-interval integral with a common derivative bound. Mathlib's actual `ProbabilityTheory.analyticAt_mgf` and `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` provide the exponential-integral and connected-equality tools, subject to their obligations being proved for this source.

Broad recent-paper searches used `subtraction`, `primitive`, `defect`, `compactification`, and `transport`. [Subtraction of infrared divergences in light-quark QCD sum rules](https://arxiv.org/html/2606.13409v1) (June 11) motivates retaining parameter-dependent terms until after integration; it supplies no FZZ theorem. [Compactification of the Fifth Painlevé Foliation](https://arxiv.org/html/2607.19285v1) (July 21), introduction and Theorem B, tracks residual data on each boundary component; this is a boundary-accounting prompt, not a vanishing or RH selector. [The Fundamental Limits of Valid Transport Map Estimation](https://arxiv.org/abs/2606.30574) (June 29) concerns statistical transport estimation and supplied no applicable proof ingredient.


## Historical comparison prefix

The initial prefix of `/tmp/fzzp_plane_gamma_match.lean` passed cleanly before the full continuation argument was added. That prefix proved real analyticity of the reciprocal Gamma function, analyticity of Gamma at positive arguments, and analyticity in `alpha` of the proposed cleared partner whenever `alpha>-3` and `alpha+beta<-2`. It also proves the exact original ball power integral for `alpha>-2` and equality of `FP0` with the unsubtracted original local integral in that range. These are checked private prefix lemmas, not a completed Gamma-equality module.

Those remaining comparison steps are now closed: reflection gives the second local identity, the ordinary whole-plane Beta integral identifies the convergent source, Gamma recurrence clears the poles, and two connected analytic slices give the first-strip identity. The physical mixed Ward law remains unproved.


## Original Gamma continuation result

`formal/GaloisForLFunctions/RHTower/FZZCigarPlaneScreeningGammaContinuation.lean` proves four data-only public statements: equality of the explicit cleared source with the cleared Gamma value; equality of the original finite part with the Gamma continuation; strict negativity throughout both first continuation strips; and the independently removed original cutoff limit with that exact Gamma value. No source analyticity, continuation identity, positivity or Ward hypothesis is supplied as a premise.

The first analytic extension holds beta in `(-2,0)` and uses alpha base point `-2-beta/2` in the ordinary chamber. The second holds alpha in `(-3,-2)` and uses beta base point `-1`. Both target intervals are connected, and the source and partner are proved analytic on them. Reciprocal Gamma, rather than Gamma itself at its poles, crosses the reciprocal zero.

Validation so far: complete scratch check clean; leaf-only build passed (8843 dependency jobs, leaf 218 seconds). All four public axiom closures in `/tmp/fzzp_plane_gamma_match_axioms.lean` contain only `propext`, `Classical.choice`, `Quot.sound`; the check passed. Formal lint found five unrelated unreachable modules in the concurrently edited Sieve and WeightedMinimax areas; it reported no new FZZ module error. No umbrella build was run. Logs: `/tmp/fzzp-plane-gamma-match-{scratch,build,axioms,lint}.log`.

Next mathematical attack is recorded in [the continued marked-source card](fzz-p-continued-screening-mark.md). It retains both original local integrals, the exterior and the derivative of the power counterterm; the complete Ward producer remains open.

Further deep/method searches `analytic equality connected interval open overlap pole removal`, `differentiate subtracted integral logarithm counterterm`, and `digamma increment concave decreasing derivative` returned partial generation 823339 with incomplete semantic/compiler coverage and retrieval timeouts. All candidate and method names were inspected. The first search's applicable identity-theorem pattern in `MobiusLaplaceCriterionFrontier.lean` requires source analyticity; the present proof supplies that obligation from the original source. No generated ingredient set closes the Ward law.

Broad recent-paper searches used `residue`, `gluing`, `localization`, and `conditioning`. [Residue ideals of hyperplane arrangements](https://arxiv.org/html/2606.16091v1) concerns logarithmic-form residues and ideal decompositions and supplied no source-continuation theorem. [One-loop five-point gluing analytically evaluated](https://arxiv.org/html/2606.13665v1) (June 11) converts residue series to Euler integrals and retains all gluing processes; its coupled rapidity Gamma factor suggests a future full-source comparison, but its four-dimensional supersymmetric theory is not an identified FZZ source. [Map-Free Single-Anchor Position Localization](https://arxiv.org/abs/2609.08370) (September 8, revised September 9) concerns covariance-weighted signal positioning; the inspected abstract supplies no usable analytic or Ward ingredient.

Lint recheck after concurrent umbrella changes still fails on four other modules: `Sieve.MenonHarmonicRamareLadderSwapped`, `Sieve.MenonHarmonicRamareLadderSwappedVolume`, `HTGeometry.WeightedMinimax.Alternation`, and `HTGeometry.WeightedMinimax.Perturbation`. Log `/tmp/fzzp-plane-gamma-match-lint-recheck.log`. This is a shared-tree gate failure, not a successful global lint audit.

The [continued-source response and sign audit](fzz-p-continued-screening-mark.md) now closes the original exponent derivative, its exact Gamma response, a positive normalized diagonal lower bound and a strictly negative actual diagonal mark. Its six public theorems passed both leaf builds and every axiom check. Together with this Gamma-matching leaf, ten public source theorems are checked. The original marked cutoff limit and its derivative interchange are now proved in the same card. Complete physical parameter transport, higher collision subtractions, independently fixed phase frame and full Ward producer remain open.
