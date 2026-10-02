# TG-C9.7–C9.8: theta domain classification and complete balanced cubic cancellation

- **ID:** TG-C9.7-C9.8-20261002-01a0
- **Stage:** 3-formalized
- **Leaves:** `PrimeBurnolFourierJetThetaDomain`, `PrimeBurnolFourierJetBalancedCubic`
- **Research parent:** `../1-in-progress/tg-fourier-jet-theta-cubic-domain.md`

## Exact new results

Physical Fourier on the two actual jet outputs implements source-channel swap S
isometrically, preserving the completed even source graph G. On the original admitted
domain the actual single-prime theta polarization is
`Q=c²I+(v²-c²)N+vcS`, with the original sech/tanh visibility and contrast.
Its graph bound exists exactly when v²=c². The source frame and its inverse orientation
are certified. The cubic displacement satisfies `(Q-N)³=c²(Q-N)` and has a graph bound
exactly at theta parameter a=0; for every nonzero a it is unbounded even on that prime's
literal depth core.

This does NOT imply that the complete modular cubic is unbounded. The full finite
Gram of the TWO ACTUAL JET OUTPUTS is positive definite, with every prime/Fourier
cross term retained, and commutes with source swap. Actual Fourier-pair independence
proves positivity without any inverse premise. At balance, Q is a scalar combination
of I and swap, so the entire Gram fixes Q under modular conjugation. The complete
associator `(R-N)³-(R-Q)³-(Q-N)³` is therefore zero because R=Q.

Unconditional existence theorem: for EVERY prime there is a positive theta parameter
such that EVERY finite injective depth packet at that prime has complete cubic zero,
while the cubic displacement has no uniform graph bound on that SAME prime core.
The coefficient matrix's action on every literal source column is proved, as are
its frame factorization and inverse; no abstract replacement frame is used.

A fixed theta parameter balances at most one prime. Thus this cancellation cannot be
applied independently prime by prime while claiming a common mixed-prime parameter.

## Paper mechanism and provenance

Evenness of the actual maximal position-square images and Fourier involutivity give
`E(g,f)=(F E(f,g).1,F E(f,g).2)`. Bounded identity and swap terms cannot cancel a
nonzero scalar multiple of the previously proved unbounded neutral N. Exact 2-by-2
projection algebra then gives the cubic displacement reduction and its coefficient
`-2c⁴` in front of N. Literal core recovery uses the previously certified single-prime
neutral obstruction, not ordinary L2 density.

The finite Gram is the first-output Fourier-pair Gram plus the second-output Gram.
The first is positive definite and the second positive semidefinite. Fourier isometry
on both outputs gives full swap commutation. Surjectivity of actual tanh from the
positive half-line onto (0,1) supplies a positive balancing parameter. Same-sign tanh
values, tanh injectivity and prime-log injectivity prove prime uniqueness at balance.

The input-and-output graph norm is the topology for extension. It is kept separate
from the two-output Gram defining the finite cubic density. The helper named
`primeBurnolFourierJetConstantThetaCubic` has a constant theta block; its actual
single-prime specialization is `primeBurnolFourierJetSinglePrimeCubic`. Neither is
silently used for the varying-prime theta action on a mixed packet.

## Verification

- Both new leaves pass foreground `lake --old env lean <leaf> -o <matching olean>`
  without warnings/errors. PrimeCore also passes after exposing its existing even-image
  theorem; it retains its existing informational ring_nf suggestion.
- Separate /tmp audit passes all 29 added/exposed public theorems, with only
  propext, Classical.choice and Quot.sound.
- RHTower imports both leaves; no umbrella or full build. Index refresh exits zero;
  scoped whitespace checks clean. No heartbeat increase, numerical experiment,
  subagent, new axiom, hole, commit or push.
- Authoritative lint exits one only for ten unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
  MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
  No new TG leaf error; existing large-file warnings remain.

## Remaining hard problem

The complete varying-prime cubic and its common domain remain open. The follow-up
`tg-prime-theta-graph-closure.md` now certifies exact two-prime theta closure and
nonclosability at every nonzero parameter. Next attack:
`../1-in-progress/tg-fourier-jet-mixed-cubic-closure.md`. Single-prime cancellation
does not provide Gamma–Xi identification, Hardy-index transfer or an arithmetic
sub-unit producer. RH remains unproved and unfalsified.
