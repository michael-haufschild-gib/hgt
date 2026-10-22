# Theta C5 center velocity: second-likelihood reserve

- **ID:** `C5-VP1-SR`
- **Stage:** 3-formalized
- **Type:** THEOREM / SIGNIFICANT PREMISE DISCHARGE (Lean)
- **Status:** `[LEAN-PROVED]` / `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `docs/drafts/pipeline/1-in-progress/theta-cusp-c5-orbit-first-contact.md`

## Exact theorem

At every `t>0`, define the first-atom-curvature core by retaining the actual center action and
actual first action jet but replacing the actual second jet by twice the first-atom Born--Witten
log curvature.  Lean proves

`firstAtomCurvatureCore(t) < masterReservedCore(t) < literalActionCore(t)`.

Therefore nonnegativity of `firstAtomCurvatureCore(t)` implies strict positivity of the literal
modular-center C5 velocity.

## Mechanism

Writing `A` for center action, `q₁` for its terminal derivative, `v=t*q₁`, `R=exp(A)-1`, and `g₂`
for likelihood curvature, exact expansion gives

`masterReservedCore`
`= firstAtomCurvatureCore + 2t*g₂*(R*(30t+15v-1)+3v)`.

Theta log-curvature positivity makes center action convex, so `0<A≤v`.  Lean proves the universal
action inequality

`0 < R*(30t+15v-1)+3v`.

When the affine coefficient is nonnegative this is immediate.  When it is negative, its own sign
forces `v<1/15`; `exp(v)<1/(1-v)` then gives `R<3v`, and multiplication by the negative coefficient
reverses the inequality to a strictly positive remainder.  Since `g₂>0`, second likelihood
curvature is strictly favorable rather than merely harmless.

## Lean artifact

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureVelocitySecondLikelihoodReserve`
- Universal coefficient theorem:
  `RHTower.c5VelocitySecondLikelihoodCoefficient_pos`
- Action--terminal-velocity law:
  `RHTower.thetaCuspReflectedLogAction_zero_le_t_mul_jetOne`
- Exact decomposition:
  `RHTower.thetaCuspCenterFifthRootVelocityMasterReservedCore_eq_firstAtomCurvature_add`
- Strict second reserve:
  `RHTower.thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_lt_masterReservedCore`
- Route-facing reduction:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_of_firstAtomCurvatureCore_nonneg`

## Novelty and RH-chain consequence

Corpus search found the necessary curvature, action derivative, and likelihood identities but no
theorem controlling this exact C5 coefficient.  The August 2026 literature audit found
Planat--Solé's second-level kernel concavity theorem (arXiv:2608.19160), but no fifth-root velocity
law or this action reserve.  Scientific priority remains provisional pending independent review.

This discharges the complete second-likelihood-curvature burden in

`C5-VP1`
→ no negative stationary witness
→ modular-center source C5
→ off-center/direct-J rank-four assembly
→ higher-packet no-escape
→ CLG/TTF or Weil positivity
→ RH.

Together with `C5-VP1-LR`, every second and third likelihood cumulant has been removed.  Exact
remaining premise is unconditional nonnegativity of
`thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore` for all `t>0`; it contains only actual
action, actual first jet, and explicit first-atom curvature/third jet.

## Verification

- direct source check with `lake env lean`
- targeted build of
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureVelocitySecondLikelihoodReserve`
- umbrella import present
- `#print axioms` on universal coefficient, action law, strict reserve, and route-facing theorem
- formal lint recognizes the new module as reachable; unrelated pre-existing unreachable-module
  findings remain elsewhere in the worktree

All audited declarations use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
No conjectural premise, added axiom, `sorry`, `admit`, `opaque`, `unsafe`, computation, or heartbeat
increase occurs.
