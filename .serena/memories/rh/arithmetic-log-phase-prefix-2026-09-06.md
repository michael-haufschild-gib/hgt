# Constant-speed prefix law and the open logarithmic-clock target

RH remains unproved. No new zero-specific unit-head identity, radical architecture, or novelty claim was obtained. Do not present this as an RH proof. Banned classic/spectral/Gamma routes were not adopted. The new mathematics was derived from actual corpus Bernoulli-cell formulas and finite phase primitives.

## Formal result, fully audited
`formal/GaloisForLFunctions/RHTower/ArithmeticLinearPhasePrefix.lean` (about 390 lines), namespace `RHTower.DeletionMixedRefinement`, imports only ZetaCentredSawtoothContinuation, mathlib Floor and Deriv.MeanValue. One definition + eleven public theorems.
For b(x)=(fract(x)^2-fract(x))/2, H(lambda,A)=integral_0^A b(x)sin(lambda*x) dx, Lean proves H<=0 for ALL lambda in (0,2pi), ALL A>=0. At A=2pi K/lambda and r=fract A,
H=r(1-r)/(2lambda)-sin(r lambda/2)sin((1-r)lambda/2)/(lambda^2 sin(lambda/2)); H=0 iff r=0. This includes all natural K, every intermediate real cutoff, and all integer endpoint coincidences. Exact second turn [3/2,3] at lambda=4pi/3 has positive integral, restoring its negative first prefix to zero.
Names: linearPhasePrefix_nonpos (main), linearPhasePrefix_at_turn, linearPhasePrefix_at_turn_eq_zero_iff, linearPhase_second_turn_pos; other public names in formal certificate. Proof: polynomial-sine primitive on each cell, retain slope jumps, telescope finite sine sum, sin y-y cos y increasing on(0,pi), then first/second half-turn monotonicity. Constant-speed model only; no logarithmic sign transfer proved.
Scratch/source lake env lean passed without warnings. Serialized `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticLinearPhasePrefix` passed, only new leaf built (cached dependency job count8663 is NOT a full build). Wired RHTower umbrella after ArithmeticSuccessorCellPhase. All12 public declarations `#print axioms` from /tmp/rh_linear_phase_axioms.lean: only propext/Classical.choice/Quot.sound. Index refreshed, search retrieves module, lint --check-generated passed (/tmp/rh_linear_phase_lint.txt). No owned Lean process remains. No commit/push by us; shared tree was concurrently committed/edited by others.

## Current open targets
Original R unchanged: sigma>0,t>0,n>=1,t<2pi n -> Im g_s(n)<0, with g=n^-s conj(R_s(n))/[conj(s)(conj(s)+1)]. Prior memory covers exact source and RH head gap.
New card docs/drafts/pipeline/1-in-progress/arithmetic-log-phase-blocks.md freezes B1 every complete logarithmic turn<=0, B2 every prefix of complete turns<=0, for a_k=n exp(2pi k/t). B1 has strong verified numerical counterevidence; no analytic/Lean no-go for literal B1 was claimed. B2 survives numerical attack, unproved.
Independently frozen C: integral_0^V b(n exp(v)) sin(t v) dv<=0 for all V>=0, integer n>=1,0<t<2pi n. This undamped clock law is unproved. Conditional paper implication: let H(V) be that primitive. C plus strict initial negative interval and |H(V)|<=V/8 gives integral_0^infinity e^(-(sigma+1)v)H'(v)dv=(sigma+1)integral e^(-(sigma+1)v)H(v)dv<0 for sigma>-1. Positive factor n^(-2sigma-1) yields actual Im g. Thus C would suffice for R, even larger real-part range, but is NOT a closed producer.
Even C would leave RH missing: restriction t<2pi n gives no control at n=1 for high zeros. At a zero, Im g1=t(2sigma-1)/(2|conj(s)(1-conj(s))|^2). No source identity forces the needed sign. Do not re-encode this equality as new zero information.

## Computations complete
Authorized Runpod /root/rh-log-phase-blocks-20260906; all results downloaded to docs/drafts/pipeline/2-fully-proven/computations/arithmetic-log-phase-blocks/. REPORT.md explains scripts and all JSON tables.
Main64triples,504blocks: sigma .05,.5,2,8; n1,4,16,64; ratio t/(2pi n)=.3,.7,.95,.9999; up to8turns reducing when log endpoint/n>20.43positive blocks in21triples, all504prefixes negative. Example sigma.05,n16,ratio.7,k1 block+.008969302168086256...,P2=-.010656973646039...
Boundary120triples,882prefixes after explicit <=3000cells cap: sigma -1,-.5,0,.001,.5,8; n1,16,256,4096; ratio.25,.5,.75,.99,.9999; up to8turns.147prefixes per real part, all negative.441 are inside sigma>0 B2;147 at sigma=-1 test C. None zero-selected.
scan.py Hurwitz-tail + exact residual-cell primitive; dps100 growing with scale. Initial accelerator run crashed BrokenProcessPool before data; reason NOT diagnosed. Disabled mp.mp._zetasum_fast by raising NotImplementedError, invoking existing direct finite-sum fallback; no installed library modification. Successful output independently verified. boundary.py finite-cell primitives only110digits. verify.py8selected points and verify_boundary.py4selected points use split-at-integers quadrature150digits: all method differences<9e-144. Python3.8.10,mpmath1.3.0,max8workers,BLAS1. All remote jobs exited. No numerical result enters Lean.

## Records
3-formalized/arithmetic-linear-phase-prefix.md = certificate.
5-failed/arithmetic-linear-block-sign.md closes ONLY constant-speed blockwise strategy, with full prefix sign/equality law as positive survivor.
STATUS has ARITHMETIC-PHASE-001 before ARITHMETIC-CELL-001, self-contained model-scoped guidance about retained cancellation and zero-margin endpoints. Original successor phase card links new card. Frontier map not edited by us.

## Potential next serious attack
Prove or disprove actual C/B2; do not rerun the completed easy constant-speed audit. C removes real-part parameter, but changing clock x=n exp(v) changes every arithmetic-cell spacing. L has exact zero margins at integer complete-turn endpoints, so a uniform strictly negative-margin perturbation transfer is invalid. A proof of C alone must still be distinguished from the zero-specific unit-head producer. It is plausible to prove literal B1 analytically false by a high-n limit at t/n=4pi/3: normalized second logarithmic turn tends to the strictly positive constant-speed second-turn integral. This limit/source substitution was NOT formalized; do not cite it as a theorem.
