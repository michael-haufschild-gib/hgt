# EDQ critical response and normalized zeta derivative

- **ID:** EDQ-CRD
- **Stage:** 3-formalized
- **Type:** exact source identification and derivative constraint; paper proof and Lean audited
- **Source:** [full response](../3-formalized/edq-full-reflection-response.md), [second current](../3-formalized/edq-logarithmic-second-flux.md), [disk admission](../3-formalized/edq-reflection-disk-admission.md)

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. This component identifies what the retained critical logarithmic source measures after exact boundary cancellation and expresses the off-line necessary condition in that derivative coordinate.

## Source identification

Let `Z(s)=zeta(s)/(s*(s+1))`, `B(s)=-1/[2*s*(1-s)]`, and `f(s)=B(s)-Z(s)+1/[12*(s+1)]`. The existing literal full Fourier source is `F(s)=conj(f(s))` throughout the open strip. Put `c=1/2+i*t`.

The existing full cubic reflection estimate shows that the symmetric quotient `[F(c+h)-F(c-h)]/(2*h)` tends to `-L_full(t)`. Analyticity of the same literal source identifies its limit with `conj(f'(c))`. Uniqueness of limits proves `L_full(t)=-conj(f'(c))` without assuming differentiation under an unproved integral.

At `c`, `c*(1-c)=t^2+1/4` is positive real. The derivative of the rational boundary and of the exact mean is precisely the existing target `V(c)`. Consequently

`L_full(t)+V(c)=conj(Z'(c))`.

At an actual critical zero this is `conj(zeta'(c)/(c*(c+1)))`. It vanishes exactly when that zeta derivative vanishes. Thus annihilating this response would require a derivative-vanishing theorem at the zero. No such theorem is proved here.

## Off-line derivative constraint

For `delta=Re(s)-1/2`, `c=1/2+i*Im(s)`, `C(s)=normSq(conj(s)*(1-conj(s)))`, and `q=(conj(c)+1)^2`, elementary algebra gives

`V(s)-V(c)=-delta^2*R(s)`,

`R(s)=i*Im(s)*(2*Im(s)^2-1/2+delta^2)/(C(s)*C(c))+1/[12*q*(q-delta^2)]`.

Both mean factors and the exact even dependence on displacement must be retained. Every actual off-line zero therefore obeys

`norm(conj(Z'(c))-delta^2*R(s))<=delta^2/12`,

and the improved height disk gives the corresponding radius `delta^2*B(epsilon)/(2*abs(t))`. These are necessary source constraints, not a proved independent lower bound on `Z'(c)` and not RH.

The previous compensated arithmetic current, with the complete critical target and unit boundary retained, satisfies

`lim_m [criticalLogSecondCurrent(t,m)+t^2*V(c)-1/12]=t^2*conj(Z'(c))`.

This connects the literal integer-jump source to the same derivative coordinate. No separate convergence of the uncompensated sum and regular integral, or additional zero constraint, is introduced.

## Gates

- [x] Existing source formula, cubic error, analyticity, and derivative APIs inspected.
- [x] Paper identification by uniqueness of symmetric limits and exact rational cancellation.
- [x] Scratch source identification, critical-zero derivative-vanishing equivalence, and off-line quadratic target transport.
- [x] Leaf wiring, targeted build, new-only axioms, lint run, both current ledgers.
- [x] Index refreshed once; all owned processes exited; three temporary Lean sources removed.
- [ ] Global lint clean: three unrelated concurrent modules are unwired.
- [ ] Independent arithmetic comparison excluding every off-line zero; RH.

## Lean inventory and final audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticCriticalResponseDerivative`, namespace `RHTower.DeletionMixedRefinement`. 352 lines, 19 theorems and five definitions.

- `criticalResponsePoint`, `fullUnitHolomorphicSource`, `reflectionZeroTarget`, `criticalResponseQuotient`: literal critical point, analytic source, complete target, and symmetric quotient.
- `unitFullFourierSource_eq_star_holomorphic`, `differentiableAt_normalizedMinimumZeta`, `hasDerivAt_fullUnitHolomorphicSource`: full source identification and exact analytic derivative.
- `norm_criticalResponseQuotient_add_le`, `tendsto_criticalResponseQuotient`, `criticalFullLogResponse_eq_neg_star_source_derivative`: the actual source expansion and uniqueness of its symmetric limit.
- `criticalResponsePoint_product`, `criticalResponsePoint_normSq`, `reflectionZeroTarget_critical_eq`, `criticalFullLogResponse_add_target_eq_derivative`: exact critical rational cancellation.
- `criticalFullLogResponse_add_target_at_zero`, `critical_zero_response_eq_zero_iff`: actual critical-zero derivative normalization and exact vanishing equivalence.
- `reflectionTargetQuadraticCorrection`, `reflection_normSq_quadratic_difference`, `reflection_mean_quadratic_difference`, `reflectionZeroTarget_sub_critical`: complete even displacement correction, with every denominator justified in the open strip.
- `reflectionDiskSource_eq_derivative_correction`, `normalized_derivative_constraint_at_offline_zero`, `normalized_derivative_height_constraint_at_offline_zero`: actual derivative coordinate and both existing necessary zero constraints.
- `tendsto_criticalLogSecondCurrent_derivative`: complete integer-jump current reconstructs the scaled normalized derivative after exact boundary and target cancellation.

Foreground scratch passed without messages. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticCriticalResponseDerivative` compiled only the new leaf in 5.6 seconds; all dependencies were cached. The umbrella import is wired. No full or umbrella build ran.

All 24 new declarations were audited once; only `propext`, `Classical.choice`, and `Quot.sound` occur. No old declaration was re-audited. No numerical experiment or computational certificate was used.

Formal lint reported exactly three unrelated umbrella reachability errors: `ThetaCuspEffectiveFirstAtomJets`, `ThetaCuspEffectiveLikelihoodCooling`, and `ThetaCuspEffectiveSourceApproximation`. The new leaf has no lint issue; concurrent files were left untouched. Global lint is not clean. Logs: `/tmp/edq_critical_derivative.{check,build,axioms,lint,index}.log` and `/tmp/edq_critical_derivative_probe.log`.

The corpus index was refreshed once. All owned Lean processes exited, and the three temporary scratch, probe, and axiom Lean sources were removed. Logs remain available.

The derivative constraints remain necessary conditions at zeros. No independent arithmetic bound excluding them, no derivative-vanishing theorem at every critical zero, and no RH proof/falsification is claimed.
