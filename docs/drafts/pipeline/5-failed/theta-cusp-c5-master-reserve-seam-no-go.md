# Theta-cusp C5 master-reserve seam no-go

- **ID:** C5-MR-seam
- **Stage:** 5-failed
- **Type:** FALSIFIED (paper + Lean)
- **Statement killed:** Universal positivity of
  `c5CompletedMasterReservedCompensationMargin`, strongest one-scalar endpoint of C5 likelihood
  lift.

## RH proof chain killed

`master-reserved compensation > 0` → literal direct-J orientation → compact/far-tail fixed-action
C5 assembly → reflection-odd rank-four/Ptolemy wall → cofinal no-escape → CLG/TTF or Weil
polarization positivity → RH.

This does not kill literal direct-J C5 route. It kills replacing full likelihood transport by sole
master curvature.

## Exact no-go

For `0 < t < u`, let `F± > 0` be likelihood source curvatures at `u ± t` and `A± > 3` the
first-atom scales. Then

`2*A+*F+ + 2*A-*F- > 6*(F+ + F-)`.

Thus adaptive-reserved margin strictly dominates master-reserved margin throughout physical
chamber. Corpus adaptive-reserve seam theorem makes adaptive margin negative in punctured right
neighbourhood of every positive centre. Master-reserved margin is therefore negative there too.

At every centre with positive exact seam orientation, literal completed margin is simultaneously
positive while master surrogate is negative. Failure is sign-level, not estimate weakness.

## Positive survivor

Full reserve discarded by master endpoint splits exactly into:

1. strictly positive adaptive scale-gap surplus;
2. exact third-likelihood-channel residual, also strict on structural tail.

Replacement endpoint is

`completed margin > 0 ↔ master margin > -full master residual`.

Consequently surviving C5 proof must retain exact third-channel transport or prove global
projective sixth-curvature monotonicity directly.

## Novelty audit

- **Internal corpus:** no prior theorem killed master-reserved endpoint; existing no-go covered only
  adaptive-reserved surrogate.
- **Literature through 2026-08-29:** generic moment-Hankel mechanisms such as
  [arXiv:2606.31647](https://arxiv.org/abs/2606.31647) do not contain this completed theta-source
  fifth-order transport decomposition. Current Xi-kernel work reaches TP2/log-concavity and records
  higher Turan inequalities as open; no matching master/adaptive seam classification was found.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5MasterReservedSeamNoGo`
- Killing theorem:
  `not_forall_c5CompletedMasterReservedCompensationMargin_nonneg`
- Local wrong-sign theorem:
  `eventually_c5CompletedMasterReservedCompensationMargin_neg`
- Literal/surrogate separation:
  `eventually_completedCompensation_pos_and_masterReserved_neg_of_exactSeamOrientation`
- Positive survivor:
  `c5CompletedMasterResidualReserve_eq_scaleGap_add_adaptiveResidual`
- Targeted `lake build`: PASS.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint remains red only on pre-existing unrelated unreachable owned modules; new module is
  reachable from `GaloisForLFunctions.RHTower`.

## Log

- 2026-08-29 — conjecture originated from Lean corpus; paper attack completed; no-go and positive
  survivor formalized unconditionally.
