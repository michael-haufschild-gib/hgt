# FZZ-P: screening collisions and continuation

Status: local collision and finite-part proofs closed and audited in Lean, 2026-09-11. RH and the complete source Ward producer remain open.

## Chain and hard obstacle

Original theta/FZZ source occurrence → complete integrated replica–momentum Ward identity in an independently fixed phase frame → balanced delay saturation → passivity → RH. The marked radial Mellin audit preserves the original divisor and supplies no independent real-part constraint. This attack retains the omitted worldsheet screening positions and their singularities.

## Source and conjecture loop

[2402.00932v3, equations (3.30)–(3.31)](https://arxiv.org/html/2402.00932v3#S3.SS2.SSS3) contains an opposite-winding position factor

`K(k,delta,z)=|z|^(2(1-k+a(k)delta)) |z-1|^(2(1-k))`, `a(k)=2k/(k-2)`.

The paper obtains the sphere expression by a continuation of screening integrals; the torus area one-point function is a separate proposed calculation. This factor is one explicit piece of the full source, not a replacement for the screening sum, ghosts, external insertions or physical counterterm.

The real-deficit kernel used here extends the displayed first-order exponent linearly. The statements for every real deficit concern that explicit mathematical family; they do not assert a complete finite-deficit CFT action.

Conjecture A: the local collision at zero becomes integrable exactly when `delta>(k-2)^2/(2k)`. The unchanged collision at one remains nonintegrable for every real `delta` when `k>2`. Thus changing the marked exponent alone never defines an ordinary whole-plane integral.

Positive survivor: prove the exact local convergence chamber of `|z|^alpha |z-1|^beta` at each puncture, retaining the other factor. Then identify the necessary local subtractions and construct a continuation with its logarithmic marked derivative. A failure of ordinary integrability does not refute the continued CFT prescription. A finite value from Lean's totalized integral is not the continuation.

Paper mechanism for the first step: polar integration gives the sharp plane threshold `alpha>-2`. On a closed ball of radius one half about zero, the factor `|z-1|^beta` and its inverse are continuous and bounded, so multiplication preserves integrability. Translate/reflection to exchange the two punctures. This isolates which deformation actually controls each collision.

## Work plan

- [x] Verify exact two-factor local convergence chambers in Lean scratch.
- [x] Derive the physical replica threshold and unchanged-collision obstruction.
- [x] Extract and prove local finite parts at both punctures and the forced leading counterterm.
- [x] Scratch verification, final leaf build, lint and umbrella wiring.
- [x] Complete all-public axiom audit and update source ledger and route-independent facts.

## Formal artifact

`formal/GaloisForLFunctions/RHTower/FZZCigarScreeningCollisionFinitePart.lean`: 422 lines, 13 public theorems, each with data parameters only. The local power threshold and Taylor subtraction are classical; the formal result retains the displayed screening-position factor and fixes its original cutoff coefficient and limit. The full RH goal is unchanged.

`lake env lean /tmp/fzzp_screening_collision.lean` passed. Final `lake build GaloisForLFunctions.RHTower.FZZCigarScreeningCollisionFinitePart`, run from `formal/`, passed in 20 seconds for the new leaf. The 8,836 reported jobs include cached/replayed dependencies; no full or umbrella build was run. The new import is wired in `RHTower.lean`. `scripts/formal_tools.py lint` passed. All 13 public axiom checks passed in `/tmp/fzzp-screening-collision-axioms.lean`, using only `propext`, `Classical.choice`, `Quot.sound`. Logs: `/tmp/fzzp-screening-collision-{scratch,build,axioms,lint}.log`.

## Retrieval

Prior plane-screening deep/method search returned one-dimensional Beta/Gamma and Bessel-plane formulas, none for this kernel. Current search: `/tmp/fzzp-collision-integrability-search.json`. Direct mathlib sources: `integrableOn_fun_norm_addHaar`, `intervalIntegral.integrableOn_Ioo_rpow_iff`, `IntegrableOn.mul_continuousOn_of_subset`. Candidate applicability must be checked in scratch before use.

The scratch proof now closes both exact local thresholds with the other position factor retained, puncture reflection, the physical marked threshold, and nonintegrability of the whole-plane replica kernel for every real deficit. The constructive extension subtracts `|z|^alpha` at zero, leaving `|z|^alpha (|z-1|^beta-1)`. The second factor has a Lipschitz bound on the half-radius disk; its subtraction gains one power, yielding integrability for `alpha>-3`.

The exact original cutoff limit has also passed scratch. Put `R=1/2`, `epsilon=exp(-T)`, and `-3<alpha<-2`. Then

`integral_(epsilon<|z|<R) K(alpha,beta,z) + 2*pi*epsilon^(alpha+2)/(alpha+2)`

tends to

`integral_(|z|<R) |z|^alpha (|z-1|^beta-1) + 2*pi*R^(alpha+2)/(alpha+2)`.

Both terms of the original annular subtraction are integrable before splitting. Polar integration evaluates the power counterterm exactly, and dominated convergence gives the remaining integral. Reflection transports the complete statement to the puncture at one, exchanging `alpha` and `beta`. Both punctures therefore have proved local prescriptions in the diagonal range `-3<alpha=beta<-2`, corresponding to `2<k<5/2`. This does not yet assemble the exterior region or higher screening depths, and it does not establish a meromorphic family or the integrated derivative of that family.

The stronger conjecture is now closed in scratch: within corrections `D*epsilon^(alpha+2)`, a finite limit exists exactly when `D=2*pi/(alpha+2)`, and that limit is the finite part above. Subtract the already convergent prescription, multiply by `epsilon^(-(alpha+2))`, which tends to zero, and identify the surviving constant coefficient. This classifies the leading local subtraction; arbitrary finite contact terms and the complete physical prescription remain separate questions.

The next full-position calculation has a concrete paper candidate. In the absolutely convergent chamber, set `alpha=-2a`, `beta=-2b`, with `0<a,b<1<a+b`. Represent each inverse norm power by its positive Gamma/Laplace integral. Tonelli then reduces the plane Gaussian to `pi/(t+u)*exp(-tu/(t+u))`. The substitution `v=t+u`, `x=t/v` leaves a Gamma integral in `v` and `Beta(1-b,1-a)` in `x`, predicting

`pi*Gamma(a+b-1)*Gamma(1-a)*Gamma(1-b)/(Gamma(a)*Gamma(b)*Gamma(2-a-b))`.

This agrees algebraically with the displayed source formula. The original Gaussian integral, change of variables and Tonelli obligations still need Lean proofs; the formula is not yet installed as a theorem. Only after this convergent-chamber identity and analytic parameter dependence close can it identify a meromorphic continuation with the local finite parts above. Multiple simultaneous collisions and higher screening depths require additional work.

The direct predecessor [2310.02313, §4.1, equations (60)–(65)](https://arxiv.org/html/2310.02313#S4.SS1) displays the two-position integral as a Gamma ratio and explains its zero by a contour branch becoming transparent. Its contour reduction explicitly needs the arcs at the puncture and infinity to disappear. This motivates checking the convergence chamber and counterterm before transferring that formula; no contour deformation or continued Gamma identity is assumed here.

Deep/method collision query returned partial pending generation 823223; its proposed mass-square collision argument concerns another kernel and does not prove the plane threshold. The subtraction query `/tmp/fzzp-collision-subtraction-search.json` returned partial pending generation 823228 with a Qdrant timeout. All candidate and source-method names were inspected. Actual source reads of `SuzukiFinitePartTranslationBridge` and `GammaTransportKernel` support the reusable difference-times-singularity proof mechanism, with different one-dimensional kernels. The plane proof uses the checked polar threshold and C¹-to-Lipschitz theorem directly.

The continuation query `/tmp/fzzp-screening-continuation-methods.json` returned partial pending generation 823240, with Qdrant and reranking timeouts; all candidate and method names were inspected. Its analytic Taylor-factor hits concern holomorphic source germs, while the current position factor is real smooth away from a puncture. The Gaussian/Beta query `/tmp/fzzp-screening-gaussian-beta-methods.json` returned partial pending generation 823255 with no runtime errors and no proposed ingredient set. All candidate and source-method names were inspected. Actual mathlib sources provide `integral_rexp_neg_mul_sq_norm`, its integrability theorem, and `Complex.betaIntegral_eq_Gamma_mul_div`; applicability to the whole-plane screening integral is the next scratch obligation.

Broad arXiv terms were `locality`, `coalescence`, `fragmentation`, restricted to June–September 2026. [Chen, September 7, 2609.07992v1, §4.4](https://arxiv.org/html/2609.07992v1#S4.SS4) distinguishes asymptotic boundary contact from finite-time crossing using monotonicity and analyticity; its ordered finite-dimensional system is not the screening source. [Wang et al., August 21, 2608.21192v1, Appendix A](https://arxiv.org/html/2608.21192v1#A1) retains a boundary integral equation except at a special matched-mobility parameter. This reinforces checking the full boundary operator; neither source supplies the missing CFT Ward enforcement, and no numerical work was run.
