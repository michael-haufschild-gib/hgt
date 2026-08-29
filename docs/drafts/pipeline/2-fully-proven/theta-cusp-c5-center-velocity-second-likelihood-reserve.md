# Theta C5 center velocity: second-likelihood reserve

- **ID:** `C5-VP1-SR`
- **Stage:** 2-fully-proven
- **Type:** SIGNIFICANT PREMISE DISCHARGE
- **Parent:** `C5-VP1`
- **Status:** `[PAPER-PROVED]`

## Exact RH proof chain

`C5-VP1-SR`
→ remove second likelihood curvature from the center-velocity burden
→ first-atom-curvature core positivity implies `C5-VP1`
→ no negative stationary witness
→ modular-center source C5
→ off-center/direct-J rank-four assembly
→ higher-packet no-escape
→ CLG/TTF or Weil positivity
→ RH.

## Frontier audit

[CORPUS] `thetaCuspReflectedLogJetTwo_zero_eq_likelihood` gives
`q₂ = 2(C-g₂)` at the modular center.  Here `C` is first-atom Born--Witten log curvature and
`g₂>0` is likelihood log-partition curvature.  The preceding formal theorem
`thetaCuspCenterFifthRootVelocityMasterReservedCore_lt_actionCore` already removes the third
likelihood jet.  `thetaCuspLogCurvature_pos`, action differentiation, and likelihood-curvature
positivity supply all sign inputs below.  Corpus search found no theorem controlling the new exact
second-curvature coefficient.

[LITERATURE] Planat--Solé, *Second-Level Concavity of the Riemann Ξ Kernel*, arXiv:2608.19160,
proves strict log-concavity of the first Laguerre expression.  It does not state a fifth-root
curvature velocity law or the action--velocity reserve below.  Earlier Laguerre inequalities likewise
do not control this C5 coefficient.  No matching result was found in the August 2026 audit.

[CONJECTURE] Define the first-atom-curvature core by replacing the actual center second action jet
inside the lower core by `2*C`, retaining the actual action and actual first action jet.  For every
`t>0`, this core is strictly smaller than
`thetaCuspCenterFifthRootVelocityMasterReservedCore t`.

Falsifier: one positive `t` for which the exact difference is nonpositive.

Hostile verdict: `SURVIVES PRELIMINARY ATTACK`.  It is not a consequence of second-level
concavity alone, and it does not assume center C5.  Its mechanism uses the literal C5 coefficients
and removes an adverse source channel from the exact velocity rather than renaming the target.

## Dependency-closed paper proof

Fix `t>0`.  Write

- `A = thetaCuspReflectedLogAction 0 t`,
- `q₁ = thetaCuspReflectedLogJetOne 0 t`,
- `v = t*q₁`,
- `R = exp(A)-1`,
- `g₂ = thetaCuspLikelihoodSourceLogPartitionJetTwo t`, and
- `C = thetaCuspBornWittenLogCurvature 1 t`.

The center action has derivative `q₁`, whose derivative is the center second jet
`2*thetaCuspLogCurvature(t)>0`.  Hence the action is convex.  Since its value at zero is zero, its
tangent inequality at `t` gives `A≤v`.  Existing strict action and first-jet positivity give
`A>0` and `v>0`.

Set `c=30t+15v-1`.  Then

`0 < R*c+3v`.

Indeed, if `c≥0`, both summands are nonnegative and `3v>0`.  If `c<0`, then `v<1/15<1`.
Monotonicity of the exponential and the standard bound
`exp(v)<1/(1-v)` yield

`R ≤ exp(v)-1 < v/(1-v) < 3v`.

Because `c<0` and `-1<c`, multiplication reverses the first strict inequality:
`R*c>3v*c`; therefore

`R*c+3v > 3v(c+1) = 3v(30t+15v) > 0`.

Now substitute the exact center identity `q₂=2(C-g₂)` into the master-reserved core.  Direct
expansion gives

`masterReservedCore`
`= firstAtomCurvatureCore + 2t*g₂*(R*(30t+15v-1)+3v)`.

Every factor in the correction is strictly positive: `t>0`, `g₂>0`, and the bracket was proved
positive above.  Thus

`firstAtomCurvatureCore < masterReservedCore`.

Combined with the already-formalized strict inequality
`masterReservedCore < literal action core`, nonnegativity of the first-atom-curvature core implies
strict literal modular-center velocity.  No open lemma or conjectural hypothesis remains in this
proof.

## Exact remaining burden after formalization

Prove the first-atom-curvature core nonnegative for every `t>0`.  All second and third likelihood
cumulants will then have been discharged; only actual action, actual first jet, and explicit
first-atom curvature/third jet remain before `C5-VP1` closes.
