# FZZ-P: marked Fermi source and its Mellin Ward identity

Status: paper and Lean proofs closed for this source classification, 2026-09-11. RH and the complete source-framed Ward producer remain open.

## Chain and hard obstacle

Fixed theta/FZZ source → integrated mixed replica–momentum Ward identity in an independently fixed phase frame → vacuum-delay saturation → passivity → RH. The previous coupling audit evaluated a full-line Fourier response. Its spectral label is not the positive-delay Mellin label of the literal Xi divisor. This card attacks that identification directly.

## Conjecture and proof loop

Let `B(u)=exp(u−exp(u))`. Define the marked delay kernel by the original coupling integral of the first replica derivative of `fzzMarkedRadialReplicaIntegrand u 0 0 delta t` at zero deficit. Conjecture A: this kernel is `G(t)=−3t exp(t)/(1+exp(t))²`, with convergence for every real `t`.

Conjecture B: on `Re s>0`, its actual Mellin transform satisfies `M(s)=−3s F(s)`, where `F=fzzCigarParityMellin`. Proposed proof: use `f(t)=1/(1+exp(t))`, `f'(t)=−exp(t)/(1+exp(t))²`, integrate `t^s f'(t)` by parts, and prove both boundary terms vanish. Near zero use `Re s>0`; at infinity use exponential decay. Both derivative products must be integrable before splitting the integral.

If B closes, marked Mellin vanishing is equivalent to the original divisor condition throughout this half-plane. It adds no new restriction on the real part of a divisor zero. No off-line zero is assumed or constructed by this equivalence.

Positive survivor to audit: retain the exact spectral multiplication law and its differentiated form `M'(s)=−3(F(s)+s F'(s))`. Joint first/mixed vanishing then tests `F(s)=F'(s)=0`, not placement on the critical line. The full CFT source terms and phase frame still need an independent enforcement calculation.

The unit-slope kernel, its convergence, the two boundary limits and the integration-by-parts identity have now passed Lean scratch. The proposed stronger survivor is equality of analytic orders: multiplication by `−3s` preserves the complete local zero multiplicity on `Re s>0`.

## General slope: preserve the original radial source

Do not specialize the CFT level to the unit-slope case. For arbitrary `v`, put `b=exp(v)`, `c=(2+b²)/b²`, and let `G_v(x)` be the same original coupling integral of the replica derivative with radial slope `b`. The exact paper reduction is

`G_v(x)=−c b² x exp(bx)/(1+exp(bx))² = (c b/3) G(bx)`.

Mellin dilation therefore predicts

`M_v(s)=(c b/3) exp(−vs) M(s)=−c b exp(−vs) s F(s)`.

The multiplier relating `M_v` and `M` is entire and never zero, for every real `v`. It preserves convergence on the right half-plane and analytic order there. These statements, the open-strip zero equivalence with `riemannZeta`, and the derivative classification have passed Lean scratch. The source derivative is retained exactly:

`M_v'(s)=(c b/3) exp(−vs) [M'(s)−v M(s)]`.

At a common zero, the extra `−v M(s)` term vanishes; joint first/spectral-derivative vanishing still tests `F(s)=F'(s)=0`. These identities are proved from the original integrals, not defined by the desired arithmetic expressions.

The final insertion check is closed in Lean scratch: the actual mixed integral is `H_v(s)=mellin (log(t) • G_v(t)) s`. Rapid power bounds at infinity and a bounded germ at zero allow mathlib's Mellin differentiation theorem, which returns both logarithmic-weight convergence and `M_v'=H_v`. Its exact expression is `−c b exp(−vs)[(1−vs)F(s)+sF'(s)]`. Consequently `M_v=H_v=0` is equivalent to `F=F'=0`. This checks the integrated mixed operator against the original source, rather than introducing it as a derivative of a closed form.

The nested source order here is Mellin integration over positive delay after the coupling integral defining `G_v`. No exchange with a different full-CFT integration order is assumed. The vanishing positive-delay Mellin boundaries do not assert vanishing target-space radial finite-part flux. The coupling law `B`, full nonzero modes, compact winding correlator and physical radial-momentum/Mellin identification remain separate source obligations.

## Work plan

- [x] Unit-slope original marked-kernel identity and convergence.
- [x] Unit-slope weighted convergence, both boundary limits, integration by parts.
- [x] General-slope original source dilation and Mellin convergence.
- [x] Exact zero-set, analytic-order and spectral-derivative classification; audit physical scope.
- [x] Mixed logarithmic insertion convergence and original Mellin differentiation.
- [x] Scratch verification, leaf-only build, all-public axiom audit, lint and umbrella.

## Formal audit

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarMarkedFermiMellinWard.lean`, 561 lines, 26 public theorems, wired into `RHTower.lean`. Every public theorem has only data parameters, with analytic domains covered by positive exponential charts. The original source integrals occur in the definitions.

`lake env lean /tmp/fzzp_marked_mellin.lean` passed. Final `lake build GaloisForLFunctions.RHTower.FZZCigarMarkedFermiMellinWard`, run from `formal/`, passed; the new leaf took 61 seconds. Its 9,106 reported jobs include cached/replayed dependencies; no umbrella or full build was run. An initial invocation from repository root stopped before compilation because that directory has no Lake configuration. All 26 public `#print axioms` checks passed in `/tmp/fzzp-marked-mellin-axioms.lean`, using only `propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py lint` passed. Logs: `/tmp/fzzp-marked-mellin-{scratch,build,axioms,lint}.log`.

## Current evidence

Current source reads: the previous `FZZCigarFermiCouplingExchange` module (46 audited theorems), `SalemFermiModeIntegral` bounds/analyticity, and mathlib `integral_Ioi_mul_deriv_eq_deriv_mul`, `GammaIntegral_convergent`, and Mellin dilation identities. Deep/method queries `/tmp/fzzp-marked-mellin-ibp-search.json`, `/tmp/fzzp-marked-mellin-dilation-methods.json`, and `/tmp/fzzp-marked-mellin-order-methods.json` returned partial pending coverage at generations 823184, 823185 and 823190. All candidate and source-method names were inspected. The specific smooth-weight and Stieltjes integration-by-parts hits use other kernels or finite intervals; the Mellin antiderivative hit starts at one. The direct improper-integral theorem matches this source. The dilation ingredient set remained an unverified proposal. Mathlib's actual `analyticOrderAt_mul` and `analyticOrderAt_congr` have passed scratch for the nonvanishing multiplier. No source enforcement theorem was supplied by retrieval.

The next source attack retains the worldsheet position factors in [2402.00932v3, equations (3.30)–(3.33)](https://arxiv.org/html/2402.00932v3#S3.SS2.SSS3). An opposite-winding collision has power `|z|^(2(1-k))` at zero deficit. For `k>2`, its ordinary two-dimensional integral is outside the locally integrable power range. This source-reading deduction is not yet a new Lean theorem. The required continuation, its marked logarithmic derivative and complete counterterms must be justified before a Gamma/Beta expression can be used as a Ward producer. The plane-screening deep/method query `/tmp/fzzp-screening-plane-methods.json` returned partial pending generation 823212, with 2,195,343 of 2,335,335 semantic entries ready. All 20 candidate names and 20 source-method names were inspected; hits concerned one-dimensional Beta/Gamma integrals, Bessel plane kernels and general complex-plane facts, not the required screening integral. No applicable ingredient set was returned.

Broad arXiv terms: `renewal`, `coercivity`, `adsorption`, with June–September 2026 filters after narrower date-text queries returned no results. [McGinnis–Li–Mori, 2606.15443v1, June 13](https://arxiv.org/html/2606.15443v1) separates a gradient identity from a rank/coercivity condition needed for local convergence; it supplies no FZZ coercivity theorem. [Kannan et al., 2606.26655v1, June 25](https://arxiv.org/html/2606.26655v1) derives a variational surfactant model retaining solid adsorption and boundary conditions. These are prompts to retain missing source terms, not imported proof assumptions. [Silva et al., 2609.05392, September 4](https://arxiv.org/abs/2609.05392) concerns molecular adsorption calculations; no applicable analytic Ward mechanism was identified.
