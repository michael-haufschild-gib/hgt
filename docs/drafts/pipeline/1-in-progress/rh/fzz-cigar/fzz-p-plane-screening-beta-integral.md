# FZZ-P: original plane screening integral

Status: ordinary whole-plane result formalized and audited, 2026-09-11. RH remains unproved.

## Chain and obstacle

Fixed theta/FZZ occurrence → complete source Ward identity in an independently fixed phase frame → balanced delay saturation → passivity → RH. The previous collision audit constructed local finite parts and forced their leading counterterms. The complete position integral and its parameter variation remain missing. This card attacks the original whole-plane integral before continuation.

## Conjecture and proof mechanism

Let `0<a,b<1<a+b`. For the original position kernel

`K(a,b,z)=|z|^(-2a)*|z-1|^(-2b)`,

prove integrability and

`integral_C K = pi*Gamma(a+b-1)*Gamma(1-a)*Gamma(1-b)/(Gamma(a)*Gamma(b)*Gamma(2-a-b))`.

The displayed Gamma ratio in [2310.02313, §4.1, equation (60)](https://arxiv.org/html/2310.02313#S4.SS1) is the comparison target, not an assumed integral identity. The proof must retain both original collisions and the tail at infinity.

Use positive Gamma/Laplace parameters. For `z` away from zero and one, `Gamma(a)*Gamma(b)*K` is the positive double integral of `t^(a-1)*u^(b-1)*exp(-t|z|²-u|z-1|²)`. The plane Gaussian is `pi/(t+u)*exp(-tu/(t+u))`. To avoid an unproved two-dimensional Jacobian, rescale `u=t*y`, interchange the positive `t,y` integrals, and evaluate the `t` Gamma integral. The remaining integral is `y^(-a)*(1+y)^(a+b-2)`, namely `Beta(1-a,1-b)` on the positive ray. Joint integrability must be proved before using Bochner Fubini; positivity/Tonelli or the product-integrability criterion can establish it from the finite iterated integral.

Public domain chart: `a=(1+exp x)/(1+exp x+exp y)`, `b=(1+exp y)/(1+exp x+exp y)`. It covers the entire triangular convergence chamber without public proof-hypothesis binders. These are independent continuation parameters; the physical unmarked source lies outside this ordinary convergence chamber.

## Work plan

- [x] Original plane Gaussian and positive Gamma-parameter representation.
- [x] Positive-ray Beta identity and parameter integral with joint integrability.
- [x] Whole-plane source integrability and exact Gamma ratio.
- [x] Audit theorems, wire leaf module and update ledgers.

## Limits

This calculation alone does not establish analytic continuation, equality with the physical local finite parts, higher screening depths, the integrated replica derivative, the phase frame or the complete Ward law. Those obligations remain in the RH chain.

## Search record

Current deep/method query: `/tmp/fzzp-plane-beta-parameter-methods.json`. Previous source reads located mathlib's plane Gaussian, product integral criteria and Beta/Gamma identities, plus `DaiYoshikawa.gamma_mul_rpow_neg_eq_integral`. All names and applicability must be verified in scratch.


## Closed proof

`FZZCigarPlaneScreeningBeta.lean` proves five public data-only theorems: the chart bounds, coverage of the entire triangular chamber, original kernel integrability, the original Gamma integral identity, and its strict positivity. The kernel is the literal product of the two norm powers, equal by definition to the previous collision kernel at exponents `(-2a,-2b)`.

1. The scaled Gamma and positive-ray Beta integrals are obtained from the current corpus. Their positive values imply integrability through Lean's `Integrable.of_integral_ne_zero`; neither formula uses the sought plane identity.
2. Complete the square in `-t|z|²-u|z-1|²`. Translation invariance and the plane Gaussian give `pi/(t+u)*exp(-tu/(t+u))`, with integrability.
3. Let `s=a+b-1`. After the single-variable rescaling `u=t*y`, the parameter integrand is `F(t,y)=y^(b-1)/(1+y)*t^(s-1)*exp(-t*y/(1+y))`. Its original `t` integral is `Gamma(s)*y^(-a)*(1+y)^(a+b-2)`. The Beta integral proves integrability of this outer function. The measurable-product criterion therefore proves joint integrability before Fubini.
4. Transfer joint integrability back through the one-dimensional rescaling to `H(t,u)=t^(a-1)*u^(b-1)/(t+u)*exp(-tu/(t+u))`. Its double integral is `Gamma(s)*Gamma(1-a)*Gamma(1-b)/Gamma(2-a-b)`.
5. For the original joint position/parameter kernel, the plane integral is `pi*H`. The same product criterion proves joint integrability. In the reverse order, the Gamma representation is `Gamma(a)*Gamma(b)*K(a,b,z)` almost everywhere; only the two measure-zero punctures are excluded. Division by the positive Gamma constants proves both the original plane integrability and its value. No spatial region is discarded.
6. The chart inverse is `x=log((1-b)/(a+b-1))`, `y=log((1-a)/(a+b-1))`; its two-sided chamber characterization is proved in Lean.

## Verification

- Scratch: `lake env lean /tmp/fzzp_plane_beta.lean`, passed without warnings.
- Final leaf: `lake build GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningBeta`, passed; no umbrella build.
- All five public declarations: `#print axioms` in `/tmp/fzzp_plane_beta_axioms.lean`; only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`, passed. Module wired into `GaloisForLFunctions/RHTower.lean`.
- Logs: `/tmp/fzzp-plane-beta-{scratch,build,axioms,lint}.log`. No numerical experiments or new axioms.

## Searches and next attack

Deep/method searches `/tmp/fzzp-plane-beta-parameter-methods.json` and `/tmp/fzzp-plane-halfline-methods.json` returned partial indexed coverage (generations 823270 and 823280); all returned candidate/method names and ingredient sets were inspected. The applicable current sources were `HalfLineBetaKernel`, `DaiYoshikawa/SpectralZetaMellin`, mathlib's Gaussian and product-integrability APIs. Their names and use were checked in scratch.

Broad recent arXiv searches for resummation, localization and dissipation produced [2607.09337v1](https://arxiv.org/html/2607.09337v1) (July 10), whose equation (15) explicitly subtracts both endpoints, and [2608.04182v1](https://arxiv.org/html/2608.04182v1) (August 4), whose abstract reorganizes mass insertions. These are method prompts, not premises or proofs for this source. Later broad gluing/factorization searches returned no usable recent result. The current plane proof uses the verified corpus, not a literature claim as an axiom.

The next direct source calculation is the convergent logarithmic marked insertion. The current corpus supplies `ProbabilityTheory.hasDerivAt_mgf` and its all-order integrability theorem from an open exponential-moment interval. Weighting plane volume by the just-proved positive kernel and using observable `-2 log|z|` converts a first-exponent shift into that moment problem. This must be proved for the original measure and then matched to the Gamma derivative. The deep/method query is `/tmp/fzzp-plane-marked-mgf-methods.json` (partial generation 823287). Continuation and physical cutoff matching still follow afterward.


Update: the proposed original logarithmic calculation is now [formalized and audited](../../fzz-p-plane-screening-marked-derivative.md), including all logarithmic moments, actual derivatives, analyticity, first cancellation and its positive surviving next response. The active continuation conjecture is [original cutoff matching](../../fzz-p-plane-screening-cutoff-matching.md).
