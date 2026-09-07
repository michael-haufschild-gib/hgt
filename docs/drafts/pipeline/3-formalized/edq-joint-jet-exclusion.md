# EDQ joint value/slope exclusion at actual simple critical zeros

- **ID:** EDQ-JJE
- **Stage:** 3-formalized
- **Type:** combined even/odd arithmetic exclusion with actual simple-critical witnesses; Lean formalized
- **Sources:** ArithmeticEvenReflectionExclusion, ArithmeticHardyResponseCoercivity, ArithmeticCriticalResponseDerivative; Zeta23SimpleCriticalDensity (cached), importing Zeta23 at manifest revision cac1c55684ee31ed76a4c0573e974c01794851c5.

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. The even source excludes segments when Hardy amplitude has a floor. The odd source supplies complementary slope control. This component preserves critical zeros while excluding nearby off-line zeros wherever the actual first jet is nonzero.

## Current corpus provider

The current corpus has an unconditional multiplicity-aware simple-critical density provider in Zeta23SimpleCriticalDensity, including a superlinear cumulative lower bound. No new density theorem is assumed here. Finite counting and the existing superlinear bound give actual simple critical zeros above every height. Analytic order one transfers from Xi to zeta and forces nonzero Hardy derivative.

## Paper proof

Write t=Im(s), delta=Re(s)-1/2, H=hardyZ(t), J=H'+Im(k)*H, and p=c*(c+1), c=1/2+i*t. For abs(t)>=1 and s in the strip, the exact odd correction R(s) has norm at most 4: its first term is bounded by 3 using both norm-square denominator factors, and its retained mean term by 1/12. The normalization rate satisfies abs(Im(k))<=2.

At an off-line zero, the odd disk gives norm(Z'(c))<=49*delta^2/12. Thus abs(J)<=49*t^2*delta^2/2. The even theorem gives abs(H)<=7*t^2*delta^2, so abs(H')<=77*t^2*delta^2/2 and

A(t)=abs(H)+abs(H') <=48*t^2*delta^2.

Whenever A(t)>0, the explicit radius r(t)=sqrt(A(t)/(96*t^2)) is positive. A strip zero at height t within abs(delta)<=r(t) must be critical: an off-line zero would give A(t)<=A(t)/2. The conclusion deliberately retains the critical zero itself.

The actual superlinear simple-critical census yields arbitrarily high t with H(t)=0 and H'(t)!=0. At each such height the radius is positive and the preceding exclusion is nonvacuous precisely where the amplitude-floor criterion fails. The exact critical response has nonzero norm there, because its Hardy norm decomposition reduces to the squared nonzero derivative. Thus actual critical zeros with nonzero arithmetic response and positive exclusion radius occur above every height.

## Remaining coverage

No all-height first-jet floor is asserted. A critical multiple zero can have H=H'=0, so requiring a positive first jet at every height would add a simplicity obligation. Even where the radius is positive, it need not reach the strip edges. Actual cofinal witnesses and local radii do not constitute RH.

## Gates

- [x] Current ledgers and actual density provider inspected; paper constants and logic checked.
- [x] Scratch joint bound and explicit exclusion radius.
- [x] Actual cofinal simple-critical witnesses with positive radius and nonzero arithmetic response.
- [x] Leaf wiring/audit, new-only axioms, lint, and current ledgers.
- [x] Index refreshed (1 changed, 0 removed); both owned scratch sources removed; no owned Lean/lake process remains.
- [ ] Independent comparison covering all off-line zeros; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticJointJetExclusion.lean` (253 lines, 10 theorems, 2 definitions), namespace `RHTower.DeletionMixedRefinement`.
- Joint bound: `hardy_first_jet_at_offline_zero_le`.
- Radius: `hardyFirstJetRadius`, `hardyFirstJetRadius_pos`, `zero_in_hardyFirstJetRadius_is_critical`.
- Actual provider: `exists_high_simple_critical_xi`, `hardy_derivative_ne_zero_of_simple_critical_xi`.
- Actual critical noncancellation: `critical_response_ne_zero_of_simple_critical_xi`.
- Unconditional assembly: `exists_high_critical_zero_with_jet_exclusion`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_joint_jet.lean`, exit 0, no diagnostics.
- Final audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion`, exit 0; only this leaf built (6.3 seconds), cached dependencies. Umbrella import appended; no umbrella build.
- Axiom audit: only the 12 new declarations checked in `/tmp/edq_joint_jet_axioms.lean`, exit 0. Every dependency, including the actual simple-critical provider used by the new assembly, is confined to `propext`, `Classical.choice`, `Quot.sound`. No added axioms, admitted proofs, or computational certificates.
- Repository lint exit 1: only unrelated unreachable modules `RHTower.ThetaCuspFactoredReflectionBound`, `RHTower.ThetaCuspFactoredReflectionError`, `RHTower.ThetaCuspSharpFiniteCooling`, `HTGeometry.FirstAtomOddScaleSevenBounds`, and `HTGeometry.LogarithmicLaplaceScoreBounds`. Concurrent files left untouched.
- Cleanup: every owned check/build/axiom/index process reached a terminal state; implementation and axiom scratch sources removed, logs retained.
- Logs: `/tmp/edq_joint_jet.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`.

The definition of RH in the current Mathlib source restricts zero location and imposes no multiplicity condition. Accordingly the exclusion theorem concludes critical location for zeros inside its radius, preserving a possible zero at the center; it does not claim the whole segment is zero-free. Global arithmetic coverage remains unproved.
