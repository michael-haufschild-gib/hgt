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
- 2026-08-29 — **TWO-SIGN SUBROUTE RETIRED; parent fixed-action comparison remains open.** Exact
  self-dual modular-ODE elimination gives the first
  nonzero seam coefficient the opposite orientation.  If
  `A=-ell''(0)`, `B=-ell''''(0)`, `C=-ell''''''(0)`, then the transverse margin has leading
  coefficient `(A*C-2*B^2)/(6*A)`, while the literal completed-theta source satisfies the strict
  law `A*C < 2*B^2`.  Thus `partial_u h(0,t)<0` for sufficiently small positive `t`; the proposed
  global chamber `h<=0` is locally compatible, but its companion sufficient law
  `partial_q(vh)>=0` has the wrong seam derivative and cannot prove barrier monotonicity by this
  two-sign decomposition.  This does not refute direct fixed-action barrier monotonicity, whose
  two terms may still compensate.  Exact no-go and sharp survivor are formalized in
  `ThetaCuspActionVelocitySeamLogMinorNoGo.lean`; detailed retirement card:
  `../../../5-failed/theta-c5-fixed-action-two-sign-transport.md`.  Surviving C5 work returns to the
  direct Gaussian-deviation three-zone chain, whose hard theta-specific core is the bulk
  accumulated-action/jet coupling.
- 2026-08-29 — A broader independent scan over `0 <= u <= 20`, `10^-6 <= t <= 100` found no C5
  failure and again placed the smallest seam-normalized sample at `u=0`. This does not revive the
  retired two-sign decomposition and supplies no proof. It strengthens the case for attacking the
  direct fixed-action Jacobian `B_u q_t - B_t q_u`, and for trying first to kill it by interval
  sign tests along numerically solved exact-action level sets.
- 2026-08-29 — **DIRECT JACOBIAN SURVIVES TARGETED HOSTILE ATTACK.** A 160-digit run evaluated
  the analytic Jacobian `B_u q_t - B_t q_u` itself at 694,800 deterministic and 200,000 randomized
  points on `10^-7 <= u <= 20`, `10^-5 <= t <= 100`; every reported sign was strict positive.
  Apparent large-action negatives at 50--80 digits vanished and stabilized positive at 120--200
  digits, so they were cancellation artifacts. This is evidence only. Computation-free module
  `ThetaCuspFixedActionC5Jacobian.lean` now proves the exact two-jet balance, both partial
  derivative formulas, the determinant/Jacobian identity, and forced seam zero `J(0,t)=0`.
  Sharpened open core: prove the desingularized transverse sign `J(u,t)/u > 0` for `u,t>0`, using
  exact seam variation, compact modular/likelihood bulk certificate, and large-action asymptotics.
- 2026-08-29 — **SEAM SURVIVOR SHARPENED; GLOBAL CENTRE MONOTONICITY KILLED.** Reflection and
  one exact differentiation give
  `J_u(0,t)=q_t(F_a q_tuu+F_b q_ttuu)-q_uu(F_t+F_a q_tt+F_b q_ttt)`; every `F_q`
  contribution cancels.  Exact formal series algebra shows this scalar begins at order `t^5`.
  With `A=-L2`, `B=-L4`, `C=-L6`, `D=-L8`, its leading numerator is
  `A^2*D - 18*A^3*C + 36*A^2*B^2 - 5*A*B*C + 4*B^3`.
  The previously proved reverse velocity law supplies the positive block
  `18*A^2*(2*B^2-A*C)`, explaining why the two-sign subroute fails while direct transport can
  survive.  RunPod scan at 240 decimal digits tested 633,332 values on
  `10^-8 <= t <= 100`; all reported `J_u(0,t)>0`.  A checkpoint at 80 digits produced a false
  negative at `t=50`, while 160/240/480 digits stabilized positive.  Conversely, selected
  240-digit values at `t=10^-3` prove computationally that `J(u,t)/u` is neither globally
  increasing nor decreasing in `u`: it falls to `0.2523` of seam value at `u=0.5`, then rises
  above `21` times seam value at `u=2`, before the far-tail collapse.  Thus no one-dimensional
  centre-monotonicity reduction remains.  Full diagnostic record:
  `../2-fully-proven/computations/2026-08-29-c5-fixed-action-jacobian-seam/REPORT.md`.
  Computation-free Lean now proves all required centre parities, exact oddness of `J`, and exact
  evenness of the algebraic quotient `J/u`; no computed value is imported.  Current proof plan is
  three-region: local bivariate Taylor chamber, compact middle inequality, first-atom tail.
- 2026-08-29 — **EXACT LOCAL CERTIFICATE TARGET DISCOVERED; SCALE-HALF-LINE SHORTCUT KILLED.**
  Exact rational modular elimination identifies the `t^5` numerator as
  `-3*P12(X)/(4096*(X-6)^6)`, `X=R^2`.  It is not positive on every `X>191/10`: a later positive
  root near `56.86` makes the large-scale sign reverse.  On the actual already-proved window
  `191/10<X<20`, however, the full numerator has 13 strictly positive rational Bernstein
  coefficients.  This selects a finite computation-free proof target using existing exact scale
  bounds and shows compensation with the reverse minor is essential.  Diagnostic record:
  `../2-fully-proven/computations/2026-08-29-modular-seam-certificate-discovery/REPORT.md`.
  No coefficient or computation is admissible in Lean until the identity and sign proof are
  independently rederived on paper.
- 2026-08-29 — **DIRECT SEAM GERM AND FIBREWISE CHAMBER FORMALIZED.** Computation-free Lean proves
  the squared-radius centre linearization has zero jets below nine and positive ninth jet, equals
  the actual direct-J centre derivative for `t>0`, and yields both positive centre derivative and
  an actual punctured positive-centre direct-J chamber for every sufficiently small positive `t`.
  This is fibrewise; uniform two-variable control as `t→0` remains.
- 2026-08-29 — **EXACT COMPENSATION LAW FORMALIZED.** With division-free fixed-action transport
  numerators `H` for `v` and `P` for `v*w`,
  `4rJ = 5P-(14+10v+8v/r)H`. Hence direct-J positivity is exactly the single compensated
  inequality `(14+10v+8v/r)H < 5P`; independent signs of `H` and `P` are neither required nor
  admissible after the seam no-go. Formal card:
  `../../../3-formalized/theta-cusp-fixed-action-c5-jacobian-compensation.md`. Full RH passport remains
  direct-J → fixed-action reflection centre → Ptolemy/rank-four packets → cofinal Weil/CLG
  positivity → RH.
- 2026-08-29 — **PURE HYPERBOLIC GAUSSIAN FIRST-ATOM CORE FORMALIZED.** For
  `q=2A(cosh(2t)-1)`, `A>3`, `t>0`, the exact compensated margin
  `5P-(14+10v+8v/(exp(q)-1))H` is strictly positive. The proof derives a sharp Bose-radius lower
  tangent and reduces the whole sign to one globally positive hyperbolic odd-series certificate;
  no computation enters Lean. This closes the pure Gaussian subcore of the planned far-tail
  chamber, not the exact rational first-atom correction or likelihood perturbation. Formal card:
  `../../../3-formalized/theta-cusp-fixed-action-c5-hyperbolic-gaussian-tail-core.md`. Next hard burden is
  to prove that the corpus-exact correction
  `-log(1-lambda(A)(cosh(2t)-1))` preserves compensation on its physical same-half-line domain,
  then lift through the likelihood factorization.
