# EDQ full logarithmic response: signed flux and height decay

- **ID:** EDQ-LRH
- **Stage:** 3-formalized
- **Type:** THEOREM; paper proof and Lean audited
- **Source:** [frontier](../1-in-progress/rh-current-frontier-map.md), [complete response](edq-full-reflection-response.md)

## Full chain

Euler deletion → exact full complex zero balance → arithmetic comparison of the full logarithmic source → exclusion of off-line zeros → RH. The full source has a uniform mass bound but no height saving. This component retains its signed arithmetic derivative and proves height decay from the actual source.

## Exact source flux

Write `P(x)=bernoulliPeriodic(x)+1/12`, `Q(x)=fract(x)-1/2`, and

`W(x)=P(x)*x^(-3/2)*log(x)`.

The periodic quadratic is continuous across integer joins. Its right derivative is `Q` even at a join, so

`W'(x)=Q(x)*x^(-3/2)*log(x)+P(x)*x^(-5/2)*(1-(3/2)*log(x))`.

With `E_t(x)=exp(i*t*log(x))`, the right derivative of `W*E_t` is

`W'*E_t+i*t*P*x^(-5/2)*log(x)*E_t`.

Both boundaries vanish, and all derivative terms are absolutely integrable. The complete source response therefore satisfies the exact identity

`i*t*L_full(t)=-integral_1^infinity W'(x)*E_t(x) dx`.

The literal `Q` term retains the derivative jumps; it is not dropped or replaced by a smooth surrogate. Its sign is still part of the source comparison.

## Height bound

From `abs(P)<=1/12`, `abs(Q)<=1/2`, the derivative is bounded by

`(1/2)*x^(-3/2)*log(x)+(1/12)*x^(-5/2)*(1+(3/2)*log(x))`.

Exact power and logarithmic moments give integral `2+1/9=19/9`. Consequently

`abs(t)*norm(L_full(t))<=19/9`,

and for nonzero height `norm(L_full(t))<=19/(9*abs(t))`. The previous bound `1/27` remains available. Neither norm ceiling supplies the signed comparison excluding the exact zero-constraint disk; RH remains open.

## Lean inventory and final audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticLogarithmicResponseHeight`, namespace `RHTower.DeletionMixedRefinement`. 293 lines, 18 theorems and six definitions.

- `abs_centeredBernoulliKernel_le`, `continuous_centeredBernoulliKernel`: literal centered kernel bound and continuity.
- `criticalLogPrimitiveKernel`, `criticalLogDerivativeKernel`, `criticalLogDerivativeMajorant`, `criticalLogSourceDensity`, `criticalLogFluxDensity`, `criticalLogBoundaryTerm`: actual amplitude, arithmetic derivative, positive majorant, full source density, signed flux, and boundary product.
- `criticalLogPrimitiveKernel_one`, `hasDerivWithinAt_criticalLogPrimitiveKernel`, `abs_criticalLogDerivativeKernel_le`: unit boundary, every right derivative, and explicit majorization.
- `integrable_criticalLogDerivativeMajorant`, `integral_criticalLogDerivativeMajorant`, `measurable_criticalLogDerivativeKernel`, `integrable_criticalLogFluxDensity`: full arithmetic derivative integrability and exact mass.
- `integral_criticalLogSourceDensity`, `integrable_criticalLogSourceDensity`: identification with the complete previously reconstructed response and its integrability.
- `hasDerivAt_logHeightCharacter`, `continuousAt_criticalLogBoundaryTerm`, `hasDerivWithinAt_criticalLogBoundaryTerm`, `tendsto_criticalLogBoundaryTerm_zero`: exact phase derivative and complete boundary analysis.
- `criticalFullLogResponse_flux_identity`: signed improper integral identity.
- `height_mul_norm_criticalFullLogResponse_le`, `norm_criticalFullLogResponse_le_inverse_height`: whole-source inverse-height bound.

Foreground scratch passed; its sole stylistic warning was removed before final audit. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticLogarithmicResponseHeight` built only the new leaf in 5.9 seconds with cached dependencies. The umbrella import is wired; no full or umbrella build ran. Formal lint reported 17 unrelated unwired `HTGeometry.PolynomialODEOddCompact*` modules (`Cubic`, `Model`, `ReflectedBase`, `Reflected2/4/6/8/10`, `Remainder0` through `Remainder6`, `SourceJets`, `SourceScalars`). It reported no issue in this leaf. Those concurrent files were left untouched; global lint is not clean.

All 24 new declarations were audited once, with only `propext`, `Classical.choice`, and `Quot.sound`; no existing declaration was re-audited. The corpus index was refreshed, all owned Lean processes exited, and three temporary Lean sources were removed. No numerical experiment or computational certificate was used. Logs: `/tmp/edq_log_height.check.log`, `/tmp/edq_log_height_{probe,build,axioms,lint,index}.log`.

The response bound is unconditional in height, with a nonzero-height condition only when dividing by its magnitude. It is not an RH proof or a sign theorem for the retained derivative integral. The full reflected cubic error still has the previous height-independent bound; this component has not proved a height saving for that error.

## Gates

- [x] Corpus research; actual right derivative, moment and improper-integral APIs inspected.
- [x] Exact signed flux identity and all boundary/integrability proofs.
- [x] Complete inverse-height bound.
- [x] Scratch, leaf wiring, targeted build, new-only axioms, lint run, both ledgers, index, cleanup.
- [ ] Global lint clean: 17 unrelated concurrent modules remain unwired.
- [ ] Opposing signed source estimate at every off-line zero; RH.
