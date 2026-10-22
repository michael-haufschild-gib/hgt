# FZZ-P: original marked plane screening derivative

Status: original convergent marked family formalized and audited, 2026-09-11. RH remains unproved.

## Chain and hard obstacle

Fixed theta/FZZ source occurrence → complete integrated mixed Ward identity in an independent phase frame → balanced delay saturation → passivity → RH. The ordinary two-puncture plane integral and its Gamma value are now proved. The next missing source operation is differentiation of that original position integral; a derivative of a displayed Gamma expression alone is insufficient.

## Conjecture and attack

At any base point in `0<a,b<1<a+b`, set `K_delta(z)=|z|^(-2(a+delta))*|z-1|^(-2b)` and `X(z)=-2 log|z|`. Prove original integrability of every `X^n*K_0`, actual differentiation through the integral with successor moment, and analyticity near zero. Then evaluate the normalized first marked response from the already proved Gamma identity.

Use the original positive measure `dmu=K_0 d²z`. Almost everywhere, `K_delta=exp(delta*X)*K_0`. The open plane convergence chamber must supply an open exponential-moment interval for this exact measure. Current mathlib's moment-generating-function derivative theorem then supplies all logarithmic moments and differentiation. The chart's proved coverage gives the required general nearby convergence, without adding an integrability premise to public theorems.

## Work plan

- [x] Exact measure identification and open exponential-moment interval.
- [x] Original all-order logarithmic integrability, differentiation and analyticity.
- [x] Gamma/digamma first-response identity from the same original integral.
- [x] Scratch, leaf, full public axiom audit, lint and umbrella wiring.

## Scope boundary

These are ordinary convergent-plane statements. Physical collision exponents lie outside this chamber. Analytic continuation matched to original cutoff finite parts, higher screening depths, the phase frame and the complete mixed Ward producer remain separate unproved obligations.

## Current sources

`FZZCigarPlaneScreeningBeta.lean`; mathlib `Probability/Moments/MGFAnalytic.lean`, `IntegrableExpMul.lean`, and the density integral/integrability APIs. Deep/method search `/tmp/fzzp-plane-marked-mgf-methods.json` has partial indexed coverage, generation 823287; candidate and method names were inspected. Every API remains subject to scratch verification.


## Closed original-source results

`FZZCigarPlaneScreeningMarkedDerivative.lean` has nine public data-only theorems. With the whole-chamber chart from the preceding module, let

`M_n(delta)=integral_C (-2 log|z|)^n |z|^(-2(a+delta)) |z-1|^(-2b)`.

- Every original `M_n(0)` is absolutely integrable.
- `HasDerivAt M_n (M_(n+1)(0)) 0` holds for every natural `n`.
- `M_0` is real analytic near zero, and its `n`th derivative at zero is `M_n(0)`.
- `M_0(0)` is exactly the previously proved positive plane integral.
- Define `psi(r)=deriv Real.Gamma r / Real.Gamma r`. The normalized original first insertion is
  `M_1(0)/M_0(0)=psi(a+b-1)-psi(1-a)-psi(a)+psi(2-a-b)`.
- On `2a+b=2`, represented by chart coordinate `y=0`, `M_1(0)=0`.
- `M_2(0)>0` throughout the convergence chamber. On the first-cancellation line,
  `deriv (M_1/M_0) 0=M_2(0)/M_0(0)>0` (the positivity statement is public; the quotient derivative calculation is in its proof).

No uniqueness of that cancellation line is claimed. The shift `delta` here is an independent exponent mark, not a claimed finite-deficit CFT action or an external momentum.

## Proof and fail/pivot record

The direct source argument closes before the Gamma response is used. Original plane volume is weighted by `K_0`; the exact exponential identity holds away from the measure-zero puncture. The previously proved chart coverage supplies integrability of every sufficiently small exponent shift. This places zero in the interior of the exponential-moment domain of this exact measure. Current mathlib then proves all logarithmic moments, their derivatives and analyticity. Density integral identities transport them back to the original Lebesgue integrals.

The normalized response is identified afterward: the original integral agrees near zero with the Gamma expression, and differentiating its logarithm retains all four nonconstant Gamma terms. Algebra predicts first cancellation at `2a+b=2`; Lean proves it. The inference that this also eliminates the next variation is false: the second moment is nonnegative everywhere and strictly positive in a neighborhood of `z=2`. Original absolute integrability and positivity of the support measure prove strict positivity of its integral. Quotient differentiation then proves the positive surviving normalized-response derivative on the cancellation line.

## Verification

- Scratch: `lake env lean /tmp/fzzp_plane_marked.lean`, passed without warnings.
- Final leaf: `lake build GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningMarkedDerivative`, passed; no umbrella build.
- All nine public declarations audited in `/tmp/fzzp_plane_marked_axioms.lean`; only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`, passed. Module wired into `GaloisForLFunctions/RHTower.lean`.
- Logs: `/tmp/fzzp-plane-marked-{scratch,build,axioms,lint}.log`. No numerical experiments or new axioms.

## Next direct attack

[Original cutoff matching](../../fzz-p-plane-screening-cutoff-matching.md) specifies the next conjecture: assemble both local subtractions and the whole exterior, define the family with both collision poles explicitly cleared, prove its analytic dependence, and identify it with the continued Gamma expression. Only a proof matched to those original cutoffs can transport this marked calculation to physical exponents. The complete phase frame and mixed Ward producer remain unproved.
