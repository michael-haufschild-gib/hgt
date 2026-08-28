# Fixed-action seam transport for completed-theta C5

- **ID:** theta-c5-fixed-action-seam-transport
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** computational reconnaissance only motivated target; proof must be source-pure
- **Statement:** At equal positive reflected log action, completed-theta normalized C5 balance is minimized at modular seam.

## Goal
For
`q(u,t)=2 log F(u)-log F(u+t)-log F(u-t)` with `F=thetaCuspFullSource`, and
`B(u,t)=thetaCuspReflectedActionFifthRootCurvatureNumerator(u,t) /
(4 (exp(q(u,t))-1)^2)`, prove

`0 <= u`, `0 < s`, `0 < t`, `q(0,s)=q(u,t)` imply `B(0,s) <= B(u,t)`.

Together with seam nonnegativity, this gives global completed-source C5 nonnegativity and closes
the source inequality required by the fifth-root divided-drop route.  No sampled value or
computer-produced certificate may enter the proof.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Write `v=t q_t` and use `q` as intrinsic time.  With `r=exp(q)-1`, cumulative endpoint ratio is
`m=v/(2r)`.  Along a fixed-centre fibre,

`d v / d q = 1 + t q_tt/q_t`,

so normalized flux elasticity is

`e=(d v/dq-v-2)/2`.

Hence the exact C5 balance becomes a first-order intrinsic-action barrier

`B = 6 - v/r - v^2/r^2 + (5v/(4r)) (d v/dq-v-2)`.

Attack fixed-action transport through the level-set Jacobian

`J = B_u q_t - B_t q_u`.

Since `q_t>0`, `J>=0` on `u>=0,t>0` would make `B` nondecreasing away from seam on each action
level.  Expand `J` only after substituting exact completed-theta atom–likelihood jets; generic
second-level concavity, Riccati positivity, and local C5 positivity are known insufficient.

## Novelty / hostile audit
- Internal corpus has action, logistic-defect, projective-ratio, Gaussian-deviation, cumulative-flux,
  and atom–likelihood normal forms, but no fixed-action centre comparison or action-level Jacobian.
- Planat–Solé, *Second-Level Concavity of the Riemann Xi Kernel* (arXiv:2608.19160, 19 Aug 2026),
  proves strict second-level concavity and explicitly makes no RH claim; it does not state this
  fixed-action law.
- `SecondLevelConcavityRiccatiFifthRootNoGo.lean` proves the three source-independent inputs above
  do not force global C5.  Any proof here must use theta-specific modular/likelihood information.
- Reconnaissance suggested seam minimization but is not evidence usable in proof or Lean.

## Open core
Prove or refute `J>=0` from exact completed-theta atom–likelihood structure.  If false, extract the
sharp positive transport chamber or first sign-changing invariant before retiring the route.

## Log
- 2026-08-28 — created in 1-in-progress after internal-corpus and current-literature audit.
- 2026-08-28 — Exact intrinsic-time reduction proved.  Put `v=t q_t`, `w=v_q`, and let
  `h=v_u|_q`.  For the sign-equivalent barrier
  `K=24r+5vw-14v-5v^2-4v^2/r`, commuting fixed-action centre and intrinsic-action derivatives
  gives
  `K_u|_q = 5 (v h)_q - (14+10v+8v/r) h`.
  Therefore the source-specific pair `h<=0` and `(v h)_q>=0` is sufficient for seam
  minimization.  This is the current hard core; neither inequality is present in the corpus or
  follows from the formal generic no-go inputs.
- 2026-08-28 — The first sufficient law now has an exact seam obstruction.  With
  `S=-ell'`, `kappa=-ell''`, and
  `h=t q_tu-(q_t+t q_tt)q_u/q_t`, modular parity gives `h(0,t)=0`, while

  `partial_u h(0,t) = 2[t kappa'(t) - (kappa(t)-kappa(0))
    (1+t kappa(t)/S(t))]`.

  This is also the fixed-action derivative at the seam because `q_u(0,t)=0`.  Hence any proof of
  the proposed chamber `h<=0` on the positive-centre side must prove the displayed one-variable
  curvature-acceleration margin nonpositive for every `t>0`.  The identity and every chain-rule
  connector are unconditional in Lean; sign remains the source-specific open core.  This
  prevents hiding a two-variable transport claim behind generic Riccati positivity.
