# TT C87 — Positive source controls at fixed endpoint 1/3

- Stage: 5-failed candidate; Route TT remains active.
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.
- Lean: complete scratch proofs passed. Six production leaves/67 declarations
  staged and wired; direct/imported audits pending behind C86 dependencies.

Candidate: every nonterminal control i<19 is strictly positive at Z=1/3
for0<h<=4/5 and0<=r<=361/25. Controls0 and1 were already proved. The complete
control18 now refutes the candidate, despite positive drift.

All contributing source rows and all10 drift columns give the exact identity

    control18(h,9-r*h²,1/3)=h⁴*Q18(h,r).

Q18 has227 monomials and degree38 by9. Its first tensor certificate failed:
coefficients(3,8) and(3,9) are strictly negative. That observation alone did
not decide the value sign.

The decisive theorem instead proves the entire control strictly negative
for EVERY1/10<=h<=1/8 at r=361/25, and separately proves9-r*h²>0 there.
Writing h=1/10+t/40, the complete degree38 polynomial -Q18(h,361/25)
has an exact strictly positive uniform lower bound on0<=t<=1. Every positive
term is retained as nonnegative; every negative term is bounded below using
0<=t^j<=1. All39 monomials are accounted for. No sampled test or external
coefficient arithmetic enters the proof.

Positive structural survivor: the exact endpoint-jet decomposition

    control18(h,v,Z)=19*P(h,v,Z)-Z*P'(h,v,Z)

for the ENTIRE reduced source P. Its sharp replacement condition is

    control18(h,v,Z)>0 iff Z*P'(h,v,Z)<19*P(h,v,Z).

Both identities are formalized and audited. This isolates the missing
endpoint information: boundary positivity alone does not produce a sign
for a control at a larger endpoint. Z=1/3 may exceed the actual nonlinear
boundary Z0. C88 now strengthens the obstruction: its complete terminal
derivative is strictly negative throughout0<h<=4/5,0<=r<=361/25. The exact
endpoint-jet identity therefore forces P(h,9-(361/25)h²,1/3)<0 for EVERY
1/10<=h<=1/8. C84 gives P(...,0)>0, and continuity gives an auxiliary
source-polynomial zero in(0,1/3). All three consequences passed Lean scratch
audits with standard axioms. This is not a zeta zero or an actual-trajectory
counterexample. The root's location relative to Z0 remains open.
C84/C85 and C77 physical-boundary positivity remain intact.

Paper proof and scratch dependencies are closed. Capstones use only
propext, Classical.choice, Quot.sound. Killing theorem:
`reducedKineticControl_eighteen_fixed_endpoint_neg`. Survivor:
`reducedKineticControl_eighteen_endpoint` and
`reducedKineticControl_eighteen_pos_iff`.
Manifest: `/tmp/tt_c87_control18_production_manifest.json`.

C88 terminal sign and full-value obstruction:46 production leaves/614
declarations staged and wired; direct/imported audits pending behind C86/C87.
Manifest: `/tmp/tt_c88_terminal_production_manifest.json`. New capstones:
`reducedKineticValue_terminal_deriv_neg`,
`reducedKineticValue_fixed_endpoint_neg`,
`reducedKineticValue_window_exists_zero`.

Next hard candidate: strict decrease of the entire source toward its physical
boundary, tested through the complete negative first derivative. It may hold
despite changing curvature and failure of source controls at a larger endpoint.
Alternatively, controls at the actual nonlinear endpoint remain open.
Full source sign, quadratic, fourth gap, join/all-rank closure and RH are open.
