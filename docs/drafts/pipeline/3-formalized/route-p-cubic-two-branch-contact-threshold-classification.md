# Route P cubic two-branch contact-threshold classification

- **ID:** `CUBIC-TWO-BRANCH-CONTACT-THRESHOLD`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** completed-Xi cubic irregular-microlocal Riemann--Hilbert route
- **Statement:** On a sphere with one marked point, exactly two Puiseux branches, and one Stokes orbit, the completed-Xi cubic unit landing fibre is nonempty exactly when mutual normalized highest-difference contact exceeds `5/2`; every landing then obeys an exact charge-magnitude law.

## Goal

Solve the first multibranch inverse-landing problem left open by the single-branch Euler no-go.
Classify, rather than merely bound, the minimal coefficient-generated irregular type capable of
carrying the negative completed-Xi cubic Malgrange residual.

## Gates

- [x] 0 -> 1 in-progress: exact claim, corpus audit, parent-theory normalization
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit
- [x] 2 -> 3 formalized: exact Lean theorem, targeted check, new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent priority review

## Exact conjecture `[CONJECTURE]`

Let `d` be coefficient-generated local data on genus zero with one marked point, one Stokes orbit,
and exactly two distinct Puiseux branches on a common positive cover degree `N`.  Write

`c(d) = contactNumerator_d(0,1) / N`

for their normalized highest-difference contact, `r(x)` for common physical rank, and

`R_Xi = normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0^3 / 4 < 0`.

At unit Rees scale:

1. every compatible charge satisfies
   `4 W_unit(x) = (5 - 2c(d)) r(x)^2`;
2. the cubic landing fibre is nonempty if and only if `5/2 < c(d)`;
3. every landing satisfies the exact magnitude law
   `(2c(d) - 5) r(x)^2 = -4 R_Xi`;
4. equivalently, writing `k=contactNumerator_d(0,1)`, landing is possible exactly when
   `5N < 2k`; hence it forces the declared coefficient window `5N < 2K`.

This is an unconditional classification of the abstract irregular-microlocal landing fibre.  It
does not assert an arithmetic source-to-charge map or an actual meromorphic connection realizing
that charge.

## Internal frontier

- `[CORPUS]` `routePPrimitiveGammaJuliaStokesSingleOrbitBranchUnitReesWittForm_eulerCollapse`
  excludes the one-branch sector in genus zero and one.
- `[CORPUS]` `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_slope_gt_one`
  gives only the general declared-root bound `(K+1)/N>1`.
- `[CORPUS]` `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_slope_gt_one_add_inv_ramificationCapacity`
  strengthens this to `1+1/M<(K+1)/N`; for one orbit with two branches, `M=4`, still far below
  the proposed sharp mutual-contact threshold `5/2`.
- `[CORPUS]` search found no two-branch landing iff, exact contact threshold, or charge-magnitude
  classification.

## External frontier

- `[LITERATURE]` Arinkin's Euler--Poincare and rigidity-index formulas classify rigidity through
  local formal types and endomorphism irregularity, but contain no completed-Xi cubic target.
- `[LITERATURE]` Boalch constructs wild character varieties from irregular curves and Stokes data;
  the theory supplies the parent geometric setting, not this scalar landing classification.
- `[LITERATURE]` Hiroe--Yamakawa identify moduli of unramified irregular connections on `P1` with
  quiver varieties and give nonemptiness/dimension constraints.
- `[LITERATURE]` Jakob--Yun give current existence and rigidity criteria for isoclinic irregular
  `G`-connections with a regular singularity at the other pole.  Their hypotheses and target differ
  from the coefficient-generated completed-Xi cubic landing fibre here.

The local quadratic count is expected to normalize to standard irregular Euler/index theory and is
therefore a `[BRIDGE]`.  The sharp completed-Xi contact threshold and exact fibre nonemptiness
classification are `[NOVELTY UNVERIFIED]`.

## Hostile attack

- **Circularity:** the claim never selects a Xi divisor or assumes RH; it uses only the already
  unconditional negative scalar `R_Xi`.
- **False boundary:** at `c=5/2`, the unit form is identically zero, so the negative target cannot
  land.  For `c<5/2`, it is nonnegative.  For `c>5/2`, a real square-root charge reaches the target.
  Thus strict threshold is forced and sharp.
- **Hidden rank issue:** one orbit and two branches give `r=2u`; a negative landing has `r != 0`,
  so division by its square is valid in the necessity direction.
- **Coefficient edge cases:** cover degree is positive by `FinitePuiseuxFamily`; branch injectivity
  makes mutual contact positive, and contact numerator is bounded by `K`.
- **Parent-theory collapse:** Euler/index mechanism is known, but it does not state the completed-Xi
  target matching, exact `5/2` phase boundary, or both directions of fibre nonemptiness.
- **Significance:** this resolves the minimal multibranch abstract landing problem and identifies
  first locally viable sector.  It does not discharge Route P's arithmetic `LAND` gate.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK`; novelty remains unverified.

## Dependency-closed proof `[PAPER-PROVED]`

Write `u` for the unique local orbit charge.  Both branches map to the unique orbit.  Therefore
terminal energy is `u^2`, physical rank is `r=2u`, and every lifted branch charge equals `u`.

The `2 x 2` contact pairing has zero diagonal because self highest-difference order is zero.  Its two
off-diagonal terms are equal by contact symmetry and each equals `c u^2`.  Hence

`localWitt(u) = u^2 + (2u)^2 - 2c u^2 = (5-2c)u^2`.

There is one puncture, so genus-zero fusion coefficient is `2(1-0-1)=0`.  Unit Rees specialization
is the undeformed global Witt form.  Thus global value equals the local value, and `r^2=4u^2`
gives

`4 W_unit(x) = (5-2c) r(x)^2`.                                                    `(1)`

Suppose `x` lands at `R_Xi`.  Cubic negativity gives `R_Xi<0`; nonnegative unit Rees parameters
and landing rigidity give `r(x) != 0`, hence `r(x)^2>0`.  Equation `(1)` forces `5-2c<0`, i.e.
`c>5/2`, and rearrangement gives

`(2c-5)r(x)^2 = -4R_Xi`.                                                         `(2)`

Conversely assume `c>5/2`.  Put `A=2c-5>0`, `delta=-R_Xi>0`, and
`u=sqrt(delta/A)`.  The quotient is nonnegative, so `u^2=delta/A`.  The unique one-puncture charge
with local coordinate `u` is automatically rank-compatible.  The local calculation gives

`W_unit = (5-2c)u^2 = -A(delta/A) = -delta = R_Xi`,

so the landing fibre is nonempty.  This proves both directions and sharpness.

Finally `c=k/N` with `N>0`.  Multiplication by positive `2N` shows
`c>5/2` iff `2k>5N`.  Since coefficient construction gives `k<=K`, every landing also forces
`5N<2K`.  No proof obligation remains.

## Lean formalization `[LEAN-PROVED]`

File: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicTwoBranchContactThresholdClassification.lean`

- `routePPrimitiveGammaJuliaStokesCubicSphereUnitWittForm_twoBranchOneOrbit_contactLaw` proves
  the exact quadratic identity `4W=(5-2c)r^2`.
- `routePPrimitiveGammaJuliaStokesCubicSphereUnitLanding_twoBranchOneOrbit_chargeMagnitude`
  proves `(2c-5)r^2=-4R_Xi` for every landing.
- `nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contact`
  proves the sharp real threshold iff, including the explicit square-root converse charge.
- `nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contactNumerator`
  proves the equivalent integral phase boundary `5N<2k`.
- `routePPrimitiveGammaJuliaStokesCubicSphereUnitLanding_twoBranchOneOrbit_five_mul_cover_lt_two_mul_ceiling`
  forces `5N<2K` for every landing.

Targeted module elaboration and explicit `.olean` emission passed.  A `/tmp` `#print axioms` audit
of exactly these five public declarations returned `[propext, Classical.choice, Quot.sound]` for
each.  No umbrella build, full rebuild, or repository-wide lint was run.  Temporary scratch and
generated dependency/module `.olean` files were removed.

## No-go closure / positive survivor

- **Killed predecessor:** single-branch low-genus landing, by Euler collapse.
- **Representation lesson:** multibranch contact, not deeper single-branch slope, is first local
  coordinate capable of producing negative cubic anomaly.
- **Positive survivor:** exact two-branch contact phase diagram and charge-magnitude law.
- **Status:** exact classification and converse construction are dependency-closed and formally
  verified in Lean; novelty remains unverified.

## Log

- 2026-08-25 -- exact two-branch/one-orbit sphere classification conjectured after single-branch
  exclusion; internal and primary-literature audits completed.
- 2026-08-25 -- square-root converse and sharp boundary audit closed; promoted to Stage 2.
- 2026-08-25 -- exact contact law, sharp nonemptiness iff, magnitude law, and integral threshold
  formalized; targeted elaboration and five-declaration axiom audit passed; promoted to Stage 3.
