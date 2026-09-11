# FZZ-P: match the continued plane integral to original cutoffs

Status: conjecture and proof attack, 2026-09-11. No continued-plane theorem yet. RH remains unproved.

## Chain and obstacle

Original complete FZZ source → integrated Ward identity in an independently fixed phase frame → balanced vacuum delay → passivity → RH. The ordinary plane Gamma identity and its original all-order logarithmic marks are now formalized. Physical exponents remain outside that chamber. The next obligation is equality of a continued family with the actual two-puncture cutoff prescription, including its parameter derivatives.

## Precise target

Write `K(a,b,z)=|z|^(-2a)|z-1|^(-2b)`, `R=1/2`, and let `E(a,b)` be the integral outside the two open radius-`R` disks. For `0<a,b<3/2`, `a+b>1`, define

- `A0(a,b)=integral_(|z|<R) |z|^(-2a)(|z-1|^(-2b)-1)`;
- `A1(a,b)=integral_(|z-1|<R) |z-1|^(-2b)(|z|^(-2a)-1)`;
- for `a,b != 1`, `FP=E+A0+A1+pi*R^(2-2a)/(1-a)+pi*R^(2-2b)/(1-b)`.

The previous local collision module proves admission of `A0,A1`; the exterior admission and complete cutoff assembly still need proofs. Target: the original plane cutoff excluding both radius-`epsilon` disks, plus `pi*epsilon^(2-2a)/(1-a)+pi*epsilon^(2-2b)/(1-b)`, tends to `FP` for `1<a,b<3/2`. Prove that this `FP` equals the Gamma ratio already proved in the ordinary chamber.

## Conjecture → proposed proof mechanism

Clear the two collision poles *in the definition*:

`H=(1-a)(1-b)(E+A0+A1)+pi(1-b)R^(2-2a)+pi(1-a)R^(2-2b)`.

Do not define this across the poles by multiplying a totalized singular quotient. Conjecture: `H` is separately real analytic throughout the convex domain `0<a,b<3/2`, `a+b>1`. The proposed Gamma partner is

`pi*Gamma(a+b-1)*Gamma(2-a)*Gamma(2-b)/(Gamma(a)*Gamma(b)*Gamma(2-a-b))`.

Reciprocal Gamma must be treated as an analytic function across `a+b=2`. Equality on the ordinary chamber, then two one-variable identity-theorem arguments, would identify these families. Only afterward divide away from `a=1,b=1` and match the proved original cutoff limit.

For source analyticity: exterior terms use exponential moments. In the disk at zero, for fixed `b`, the signed regular factor is independent of `a`; split its positive and negative parts and use finite absolute exponential moments. In the disk at one, the zero subtraction is parameter-dependent. With `X=-2 log|z|`, use `exp(aX)-1=X*integral_0^a exp(tX)dt`. Here `X` is bounded and vanishes linearly at the puncture, so `|X|*|z-1|^(-2b)` is integrable for `b<3/2`. This offers a finite signed exponential-moment measure for the derivative and an analytic primitive. All domination, Fubini, analytic-primitive and identity-theorem obligations remain to be verified.

If the identity is proved, both physical exponents in `(1,3/2)` would give a negative finite part: the two `Gamma(1-a),Gamma(1-b)` factors are negative and `Gamma(2-a-b)` is negative. This is a prediction to prove, not audited knowledge or a positivity premise.

## Work plan

- [ ] Exterior integrability and original two-cutoff limit.
- [ ] Separate analyticity of the explicitly pole-cleared source.
- [ ] Analytic Gamma partner and identity-theorem match.
- [ ] Original continued marked derivative and its boundary terms.
- [ ] Leaf proofs, complete audits and route updates.

Higher Taylor subtractions, simultaneous collisions, higher screening depths, physical coupling/momentum identification and the complete Ward producer remain outside this first continuation strip.

## Current search evidence

`/tmp/fzzp-plane-finitepart-analytic-methods.json`: partial generation 823289; malformed local-model judgment and deadline, with predominantly irrelevant Hadamard-matrix methods. All returned names were inspected; no source-continuation theorem was supplied. Rephrased reciprocal-Gamma deep/method search: `/tmp/fzzp-plane-reciprocal-gamma-methods.json`. Source text already locates mathlib's `differentiable_one_div_Gamma`; applicability remains to be checked in scratch. This is a plan, not a proof certificate.


The rephrased reciprocal-Gamma search returned partial generation 823293 with complete file inventory but incomplete source/compiler and semantic coverage; all candidate/method names and the proposed ingredient set were inspected. `Complex.differentiable_one_div_Gamma` in mathlib `Gamma/Beta.lean` is an unconditional entire-reciprocal theorem. `/tmp/fzzp_plane_continuation_names.lean` now verifies its use and proves, in scratch, `AnalyticAt ℝ (fun s : ℝ => (Real.Gamma s)⁻¹) r` for every real `r`, by restricting the complex analytic function. Log `/tmp/fzzp-plane-continuation-names.log` is clean. Required real-part restriction import: `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`. The unrelated `Gammaℝ` symbol in `ZetaCarrier` is an archimedean completed Gamma factor and must not be substituted for `Real.Gamma`.

This verifies the reciprocal-Gamma component of the proposed partner. Separate analyticity of the original explicitly subtracted source and its whole-plane cutoff assembly remain unproved.
