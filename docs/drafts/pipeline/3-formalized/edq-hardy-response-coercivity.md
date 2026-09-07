# EDQ Hardy phase and two-component response control

- **ID:** EDQ-HRC
- **Stage:** 3-formalized
- **Type:** exact source decomposition, growing positive phase control, and response-zero classification; Lean formalized
- **Sources:** [critical derivative](../3-formalized/edq-critical-response-derivative.md), `HardyZPhaseAsymptotic.lean`

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. The critical response is the conjugate derivative of `Z(s)=zeta(s)/(s*(s+1))`. This component uses the actual functional-equation phase to control its two real components, rather than treating that derivative as arbitrary complex data.

## Exact source identity

Write `c=1/2+i*t`, `p=c*(c+1)`, `k=(2*c+1)/p`, `H=hardyZ(t)`, and `theta=gammaHardyTheta(t)`. Let

`beta=gammaHardyPhaseRate(t)+Re(k)`, `b=Im(k)`, `J=H'+b*H`.

The existing corpus phase identities imply

`exp(i*theta)*p*Z'(c)=-beta*H-i*J`.

Since the exponential has unit norm, and EDQ proved `L_full(t)+V(c)=conj(Z'(c))`,

`norm(p)^2*norm(L_full(t)+V(c))^2=(beta*H)^2+J^2`.

The rational coefficient has strictly positive real part:

`Re(k)=(1/2)/(t^2+1/4)+(3/2)/(t^2+9/4)>0`.

The proved Gamma phase rate tends to infinity, and the correction is strictly positive at every height, so `beta` also tends to positive infinity. In particular `beta>0` eventually. Every fixed real coefficient `B` satisfies `B*abs(H)<=norm(p)*norm(L_full+V(c))` eventually. Whenever `beta>0`, vanishing of the actual critical response is equivalent to simultaneous vanishing of `H` and `H'`, hence to `zeta(c)=0` and `zeta'(c)=0`. This is a classification of response zeros; it does not establish simplicity or exclude off-line zeta zeros.

## Off-line constraints

For the exact quadratic correction `R(s)` already proved, set

`Q(s)=exp(i*theta)*p*conj(R(s))`, `delta=Re(s)-1/2`.

Multiplication and conjugation preserve the full disk, scaling its radius by `norm(p)`. Thus every actual off-line zero satisfies the joint disk for the real pair

`beta*H+delta^2*Re(Q)`, `J+delta^2*Im(Q)`.

Both existing radii are retained. The identity controls both value and corrected slope and yields the lower bound `abs(beta*H)<=norm(p)*norm(L_full+V(c))`. A separate arithmetic comparison ruling out the required small pair is still missing.

## Gates

- [x] Current ledgers, exact critical response, Hardy phase derivative and positivity source inspected.
- [x] Paper identity, positive phase coefficient, response-zero classification, and joint off-line transport.
- [x] Scratch proofs of actual-source decomposition and joint constraints.
- [x] Leaf wiring, targeted build, and new-only axiom audit.
- [x] Current ledgers updated; repository lint run (seven unrelated wiring errors listed below).
- [x] Index refreshed (5 changed, 0 removed); all three owned scratch sources removed and no owned Lean/lake process remains.
- [ ] Independent comparison excluding every off-line zero; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticHardyResponseCoercivity.lean` (252 lines, 17 theorems, 5 definitions).
- Namespace: `RHTower.DeletionMixedRefinement`.
- Main declarations: `hardy_rotated_normalized_derivative`, `hardy_response_norm_sq`, `hardyResponseCoercivity_tendsto_atTop`, `eventually_hardy_amplitude_bound`, `eventually_hardy_response_eq_zero_iff_zeta_jet`, `hardy_reflection_source_norm_sq`, `hardy_joint_constraint_at_offline_zero`, `hardy_joint_height_constraint_at_offline_zero`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_hardy_response.lean`, exit 0, no diagnostics.
- Final audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticHardyResponseCoercivity`, exit 0; only this leaf built (4.2 seconds); dependencies replayed from cache. Umbrella import appended; no umbrella build.
- Axioms: only the 22 new declarations checked in `/tmp/edq_hardy_response_axioms.lean`; no dependencies outside `propext`, `Classical.choice`, `Quot.sound`. No admitted proof, added axiom, or computational certificate.
- Repository lint exit 1: only unrelated unreachable modules `RHTower.ThetaCuspEffectiveFirstAtomJets`, `RHTower.ThetaCuspEffectiveLikelihoodCooling`, `RHTower.ThetaCuspEffectiveReflectionApproximation`, `RHTower.ThetaCuspEffectiveSourceApproximation`, `RHTower.ThetaCuspEffectiveTailScale`, `HTGeometry.FirstAtomOddTailAlgebra`, and `HTGeometry.HankelThreePerturbation`. No edits to those concurrent modules.
- Cleanup: every owned check/build/axiom process reached a terminal state; the probe, implementation scratch, and axiom scratch sources were removed. Logs retained.
- Logs: `/tmp/edq_hardy_response.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`; initial name probe `/tmp/edq_hardy_response_probe.log`.

## Remaining producer

The complete rotated disks are invertible transports of the existing necessary conditions. They still admit the established outer-quarter high-height source region, including actual nonzeros. The new coercivity gives independent critical value/slope control and response-zero classification, but no uniform separating lower bound for the corrected pair. Simultaneous zeta and derivative zeros are permitted by the theorem; no simplicity assertion is made. A signed arithmetic comparison excluding every off-line zero remains unproved; RH remains unproved and unfalsified.
