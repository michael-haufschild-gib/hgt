# EDQ height-saving error for the complete reflected source

- **ID:** EDQ-REH
- **Stage:** 3-formalized
- **Type:** THEOREM; paper proof and Lean audited
- **Source:** [frontier](../1-in-progress/rh-current-frontier-map.md), [full response](edq-full-reflection-response.md), [height flux](edq-logarithmic-response-height.md)

## Full chain

Euler deletion → exact full complex zero balance → signed arithmetic comparison with an error preserving displacement and height → exclusion of off-line zeros → RH. The first response has height decay, but its nonlinear error does not yet. This component applies the actual arithmetic derivative to that error on every compact substrip.

## Literal residual and derivative

Let `delta=Re(s)-1/2`, `epsilon>0`, `abs(delta)<=1/2-epsilon`, `P=bernoulliPeriodic+1/12`, and `Q=fract-1/2`. Set `R(a)=sinh(a)-a`. The complete reflected error is the integral of

`-2*P*x^(-5/2)*R(delta*log(x))*exp(i*t*log(x))`.

Its integration-by-parts primitive amplitude is `U=-2*P*x^(-3/2)*R(delta*log(x))`. The exact right derivative, including every integer join, is

`U'=-2*Q*x^(-3/2)*R + P*x^(-5/2)*(3*R-2*delta*(cosh(delta*log(x))-1))`.

The corpus inequalities for `sinh(a)-a` and `cosh(a)-1`, with `cosh(a)<=exp(abs(a))`, give the absolute majorant

`abs(delta)^3 * [x^(-1-epsilon)*log(x)^3/6 + x^(-2-epsilon)*log(x)^3/24 + x^(-2-epsilon)*log(x)^2/12]`.

Its exact integral is `abs(delta)^3*B(epsilon)`, where

`B(epsilon)=epsilon^(-4)+1/[4*(1+epsilon)^4]+1/[6*(1+epsilon)^3]`.

Both primitive boundaries vanish. Right-derivative FTC and absolute integrability therefore give

`abs(t)*norm(F(s)-F(1-conj(s))+2*delta*L_full(t))<=abs(delta)^3*B(epsilon)`.

For nonzero height and displacement, every actual off-line strip zero must consequently satisfy

`norm(L_full(t)+V(s))<=delta^2*B(epsilon)/(2*abs(t))`,

with the full complex target `V` from EDQ-FRR. Every off-line strip zero of nonzero height has the canonical positive choice `epsilon=1/2-abs(delta)`, its actual distance from the strip edges. Thus the estimate applies pointwise throughout the open strip; its cost is not uniform as that distance tends to zero. The previous height-independent bound remains available. This is a tighter necessary constraint at high height, not a signed source estimate excluding it. RH remains open.

## Lean inventory and final audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticReflectionErrorHeight`, namespace `RHTower.DeletionMixedRefinement`. 431 lines, 22 theorems and eight definitions.

- `reflection_abs_cosh_sub_one_le`, `reflection_hyperbolic_substrip_bounds`: even and odd hyperbolic majorants with explicit substrip dependence.
- `reflectionCubicKernel`, `reflectionCubicPrimitive`, `reflectionCubicDerivative`, `reflectionCubicMajorant`, `reflectionCubicHeightCost`: actual source amplitude, primitive, full arithmetic derivative, and exact cost.
- `reflectionCubicPrimitive_eq_mul`, `hasDerivWithinAt_reflectionCubicPrimitive`, `abs_reflectionCubicDerivative_le`, `integrable_reflectionCubicMajorant`, `integral_reflectionCubicMajorant`: exact source derivative and its complete moment bound.
- `abs_reflectionCubicKernel_le`, `abs_reflectionCubicPrimitive_le`: displacement-sensitive source and boundary estimates.
- `reflectionCubicDensity`, `reflectionCubicFlux`, `reflectionCubicBoundary`: actual source, signed flux, and full phase-bearing boundary term.
- `integrable_reflectionCubicDensity`, `integrable_reflectionCubicFlux`, `continuousAt_reflectionCubicBoundary`, `hasDerivWithinAt_reflectionCubicBoundary`, `tendsto_reflectionCubicBoundary_zero`, `reflectionCubic_flux_identity`: every integrability, continuity, derivative, and boundary requirement for the improper integral identity.
- `height_mul_norm_reflectionCubic_integral_le`: full residual height saving.
- `fullFourier_cpow_eq_logMode`, `integrable_unitFullFourierDensity`, `unitFullFourierSource_error_eq_cubic`: exact identification with the existing complete Fourier source.
- `height_mul_norm_unitFullFourierSource_error_le`: height-saving cubic control of the complete source error.
- `norm_criticalFullLogResponse_zero_constraint_substrip_height`, `norm_criticalFullLogResponse_zero_constraint_height`: complete complex zero constraints with explicit substrip cost and canonical edge distance.

Foreground scratch passed without messages. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticReflectionErrorHeight` built only the new leaf in 5.9 seconds with cached dependencies. Its umbrella import is wired; no full or umbrella build ran. Formal lint reported 22 unrelated unwired modules in concurrent work and no issue in this leaf. All reported errors were umbrella reachability errors; those unrelated files were left untouched. Global lint is not clean.

All 30 new declarations were audited once, with only `propext`, `Classical.choice`, and `Quot.sound`; no existing declaration was re-audited. The corpus index was refreshed, all owned Lean processes exited, and four temporary Lean sources were removed. No numerical experiment or computational certificate was used. Logs: `/tmp/edq_error_height.check.log`, `/tmp/edq_error_height_{probe,build,axioms,lint,index}.log`.

The bound controls the complete complex error, not just a projected component. It does not prove a sign for its retained flux or a strict separation of the actual logarithmic response from the zero target. The inverse fourth-power dependence on distance to the strip edges belongs to this proved majorant; it is not a source divergence theorem. RH remains unproved.

## Gates

- [x] Current corpus, ledgers, right-derivative and hyperbolic source evidence inspected.
- [x] Literal residual identity, exact derivative, compact-substrip majorants and moments.
- [x] Both boundaries, exact full-source flux identity, height-saving cubic error.
- [x] Complete complex zero constraint with the improved radius and canonical edge distance.
- [x] Scratch, leaf wiring, targeted build, new-only axioms, lint run, both ledgers, index, cleanup.
- [ ] Global lint clean: 22 unrelated concurrent modules remain unwired.
- [ ] Strict signed source comparison excluding every off-line zero; RH.
