# Intrinsic-action velocity normal form for completed-theta C5

- **ID:** theta-c5-action-velocity-normal-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** theta-c5-fixed-action-seam-transport
- **Statement:** Completed-theta C5 is exactly a first-order intrinsic-action velocity barrier.

## Goal
Replace cumulative endpoint mass and local flux elasticity by one action velocity field and its
intrinsic derivative, exposing exact fixed-action transport burden without sign loss.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete algebraic paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module built, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Theorem
Let `q` be reflected completed-theta log action, `r=exp(q)-1`,
`v=t q_t`, and `w=dv/dq`.  At every positive displacement,

`m = v/(2r)`,

`e = (w-v-2)/2`,

and the action C5 numerator is

`r * (24r + 5vw - 14v - 5v^2 - 4v^2/r)`.

Since `r>0`, C5 nonnegativity is equivalent to nonnegativity of the parenthesized first-order
barrier.

## Proof
`q_t>0` follows from strict completed-source log concavity.  Differentiate `v=tq_t` to obtain
`dv/dq=(q_t+tq_tt)/q_t`.  Substitute `A=P r`, `D=P q_t`, and
`J=P(q_tt-q_t^2)` into definitions of `m`, `e`, and C5.  Cancellation of positive product factor
and elementary field algebra give displayed identities.  No estimate or external certificate is
used. `[PROVED HERE]`

## Lean certificate
- Module: `GaloisForLFunctions.RHTower.ThetaCuspReflectedActionVelocityBalance`
- Main theorem:
  `thetaCuspReflectedActionFifthRootCurvatureNumerator_nonneg_iff_actionVelocityBarrier`
- Targeted build: PASS
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`

## Consequence
At fixed action, writing `h=partial_u v|_q`, direct differentiation yields

`partial_u K|_q = 5 partial_q(vh) - (14+10v+8v/r)h`.

Thus `h<=0` and `partial_q(vh)>=0` form an exact sufficient source-specific transport chamber.
These remain open and are tracked by `theta-c5-fixed-action-seam-transport.md`.

At the modular seam, the first transport law has the exact source-jet boundary

`h(0,t)=0`,

`partial_u h(0,t)=2[t kappa'(t)-(kappa(t)-kappa(0))(1+t kappa(t)/S(t))]`,

where `S=-ell'` and `kappa=-ell''`.  Since `q_u(0,t)=0`, ordinary and fixed-action centre
derivatives agree there.  Lean theorem
`hasDerivAt_thetaCuspReflectedActionVelocityFixedActionCenterTransport_zero` closes this reduction
without a sign premise.

## Log
- 2026-08-28 — paper proof closed, Lean formalization built, axiom audit passed.
- 2026-08-28 — exact seam transverse-transport margin added and formalized; its global sign is the
  sharpened open source law.
- 2026-08-29 — exact seam minor eliminated by the self-dual modular ODE and Bell transfer.  The
  new formal theorem `thetaCuspActionVelocitySeam_curvature_sixth_lt_two_fourth_sq` proves
  `A*C<2*B^2`, and `not_thetaCuspActionVelocitySeamLogMinor_nonneg` closes the forward-orientation
  no-go.  Module `ThetaCuspActionVelocitySeamLogMinorNoGo` is wired and targeted-build green;
  axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.
